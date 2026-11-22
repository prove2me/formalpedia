-- Prove2me | Theorems.Thm_SobolevL2_sobolevNorm_eq_iInf_fourier
-- name    : SobolevL2.sobolevNorm_eq_iInf_fourier
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:46.553833+00:00
-- url     : https://prove2.me/theorems/b649ccae-4ea0-4af1-a2ef-e3565403cf9a
-- title:
--   The $H^s$ norm is the weighted Fourier-side norm: $\|u\|_{H^s}=\|(1+|\xi|^2)^{s/2}\,\widehat u\|_{L^2}$ for every tempered distribution $u$
-- statement:
--   **Fourier-side description of the $H^s$ norm.** Let $E$ be a finite-dimensional real inner product space (a copy of $\mathbb R^n$, $n=\dim E$) with its Lebesgue measure, let $F$ be a complex Hilbert space (the classical case is $F=\mathbb C$), and let $\mathcal S(E,F)$, $\mathcal S'(E,F)$ be the Schwartz functions and the tempered distributions. The Fourier transform is $\widehat f(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$, extended to $\mathcal S'$ by duality. For $s\in\mathbb R$ the Sobolev (Bessel potential) space is $H^s(E,F)=\{u\in\mathcal S'(E,F):\ (1+|\xi|^2)^{s/2}\widehat u\in L^2\}$, and $\|u\|_{H^s}=\|J^s u\|_{L^2}\in[0,\infty]$, where $J^s$ is the Fourier multiplier with symbol $(1+|\xi|^2)^{s/2}$; by convention $\|u\|_{H^s}=\infty$ when $u\notin H^s$ (definition `SobolevL2.sobolevNorm`).
--
--   Then for every $u\in\mathcal S'(E,F)$ and every $s\in\mathbb R$,
--   $$\|u\|_{H^s}=\big\|(1+|\xi|^2)^{s/2}\,\widehat u\big\|_{L^2(E,F)},$$
--   where the right-hand side is $\infty$ unless the tempered distribution $(1+|\xi|^2)^{s/2}\widehat u$ is an $L^2$ function. In particular $u\in H^s$ if and only if $(1+|\xi|^2)^{s/2}\widehat u\in L^2$, and then $\|u\|_{H^s}^2=\int_E(1+|\xi|^2)^s|\widehat u(\xi)|^2\,d\xi$.
--
--   This is the definition of the Sobolev norm through the weight on the dual group, (9.1.1.3) in Definition 9.1.1.1 of the source and the identification $H^s_w=L^2(\widehat G,(1+w^2)^{s/2}\mu_{\widehat G})$ in the proof of Lemma 9.1.1.2, for $G=\mathbb R^n$ and $w(\xi)=|\xi|$. In the paper's normalization (9.1.1.3) the squared norm carries the weight $(1+w^2)^{s/2}$ (not $(1+w^2)^{s}$); for $G=\mathbb R^n$, $\widehat G\cong\mathbb R^n$ and the Sobolev weight $w(\xi)=|\xi|$ (which satisfies (9.1.1.2) with $C_w=1$), the paper's $H^s_w$ is therefore the classical $H^{s/2}$ used here.
--
--   **Formalization Note.** $E$ carries `volume` (Lebesgue measure of the inner product space), tempered distributions are Mathlib's `𝓢'(E, F)`, the Bessel potential is `TemperedDistribution.besselPotential` and membership in $H^s$ is Mathlib's `TemperedDistribution.MemSobolev s 2`. The norm `SobolevL2.sobolevNorm s u : ℝ≥0∞` is $\infty$ off $H^s$, so statements in $[0,\infty]$ cover membership and the norm at once. The right-hand side is the infimum of `‖g‖ₑ` over the (at most one) `g ∈ L²` with `smulLeftCLM F (fun ξ ↦ (1 + ‖ξ‖²)^{s/2}) (𝓕 u) = g`, i.e. it is $\|(1+|\xi|^2)^{s/2}\widehat u\|_{L^2}$, and $\infty$ when no such `g` exists. Mathlib's `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier` is the corresponding statement about membership only; the equality of norms is Plancherel's theorem.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 396, Definition 9.1.1.1, (9.1.1.3), and Lemma 9.1.1.2 (identification $H^s_w=L^2(\widehat G,(1+w^2)^{s/2}\mu_{\widehat G})$), specialized to $G=\mathbb R^n$, $w(\xi)=|\xi|$; classical reference: P. Górka and E. G. Reyes, Sobolev spaces on locally compact abelian groups, arXiv:1208.3053v1 (2012), §§1–2, as cited by the paper at Definition 9.1.1.1

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

namespace SobolevL2

/-- For every tempered distribution `u` and every `s : ℝ`, the Sobolev norm `‖J^s u‖_{L²}` equals the
`L²` norm of `(1 + ‖ξ‖²)^{s/2} • 𝓕 u` (both sides are `∞` when the distribution in question is not
an `L²` function). -/
theorem sobolevNorm_eq_iInf_fourier {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (u : 𝓢'(E, F)) :
    sobolevNorm s u =
      ⨅ (g : Lp F 2 (volume : Measure E))
        (_ : smulLeftCLM F (fun ξ : E ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 u) = g), ‖g‖ₑ := by
  sorry

end SobolevL2
