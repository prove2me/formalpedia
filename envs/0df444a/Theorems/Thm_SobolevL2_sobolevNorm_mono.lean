-- Prove2me | Theorems.Thm_SobolevL2_sobolevNorm_mono
-- name    : SobolevL2.sobolevNorm_mono
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:46.320865+00:00
-- url     : https://prove2.me/theorems/60d82aad-a9f5-4e4b-abb3-d3fff040a3a7
-- title:
--   Monotonicity of Sobolev norms: $\|u\|_{H^t}\le\|u\|_{H^s}$ for $t\le s$, hence $H^s\subset H^t$ continuously and $H^s\subset L^2$ for $s\ge0$
-- statement:
--   **Monotonicity of the $L^2$ Sobolev scale.** Let $E$ be a finite-dimensional real inner product space (a copy of $\mathbb R^n$, $n=\dim E$) with its Lebesgue measure, let $F$ be a complex Hilbert space (the classical case is $F=\mathbb C$), and let $\mathcal S(E,F)$, $\mathcal S'(E,F)$ be the Schwartz functions and the tempered distributions. The Fourier transform is $\widehat f(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$, extended to $\mathcal S'$ by duality. For $s\in\mathbb R$ the Sobolev (Bessel potential) space is $H^s(E,F)=\{u\in\mathcal S'(E,F):\ (1+|\xi|^2)^{s/2}\widehat u\in L^2\}$, and $\|u\|_{H^s}=\|J^s u\|_{L^2}\in[0,\infty]$, where $J^s$ is the Fourier multiplier with symbol $(1+|\xi|^2)^{s/2}$; by convention $\|u\|_{H^s}=\infty$ when $u\notin H^s$ (definition `SobolevL2.sobolevNorm`).
--
--   If $t\le s$ are real numbers, then for every $u\in\mathcal S'(E,F)$
--   $$\|u\|_{H^t}\le\|u\|_{H^s}.$$
--   Consequently $H^s(E,F)\subset H^t(E,F)$ and the inclusion is a continuous linear map of norm at most $1$. For $t=0$, where $\|u\|_{H^0}=\|u\|_{L^2}$, this says that for $s\ge0$ every element of $H^s$ is an $L^2$ function and $\|u\|_{L^2}\le\|u\|_{H^s}$.
--
--   These are Proposition 9.1.1.3(1) (the inclusion $H^s_w\to L^2$, (9.1.1.4)–(9.1.1.5)) and Proposition 9.1.1.3(2) ((9.1.1.6) and the continuity of $H^{s'}_w\subset H^s_w$ for $s'>s$) of the source, for $G=\mathbb R^n$ and the weight $w(\xi)=|\xi|$; the source refers to [GR, Prop. 1, 2] for them. In the paper's normalization (9.1.1.3) the squared norm carries the weight $(1+w^2)^{s/2}$ (not $(1+w^2)^{s}$); for $G=\mathbb R^n$, $\widehat G\cong\mathbb R^n$ and the Sobolev weight $w(\xi)=|\xi|$ (which satisfies (9.1.1.2) with $C_w=1$), the paper's $H^s_w$ is therefore the classical $H^{s/2}$ used here.
--
--   **Deviation from the source.** In (9.1.1.6) the source quantifies over $f\in H^s_w$ (the larger space) while the inequality and the inclusion concern the smaller space $H^{s'}_w$ (erratum I93 of the riemann-masullo formalization, https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md); the corrected statement, from the higher degree to the lower one, is formalized. The source assumes $s\ge0$ throughout Proposition 9.1.1.3; the inequality holds for all real $t\le s$, which is the classical statement for the Bessel potential scale.
--
--   **Formalization Note.** $E$ carries `volume` (Lebesgue measure of the inner product space), tempered distributions are Mathlib's `𝓢'(E, F)`, the Bessel potential is `TemperedDistribution.besselPotential` and membership in $H^s$ is Mathlib's `TemperedDistribution.MemSobolev s 2`. The norm `SobolevL2.sobolevNorm s u : ℝ≥0∞` is $\infty$ off $H^s$, so statements in $[0,\infty]$ cover membership and the norm at once. When $u\notin H^s$ the right-hand side is $\infty$ and the inequality is trivial; when $u\in H^s$ it gives both $u\in H^t$ and the norm bound.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 396–397, Proposition 9.1.1.3(1)–(2), (9.1.1.4)–(9.1.1.6) (see Remark 9.1.1.4), specialized to $G=\mathbb R^n$, $w(\xi)=|\xi|$; classical reference: P. Górka and E. G. Reyes, Sobolev spaces on locally compact abelian groups, arXiv:1208.3053v1 (2012), Prop. 1 and Prop. 2, as cited by the paper in Remark 9.1.1.4

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

namespace SobolevL2

/-- For `t ≤ s` and every tempered distribution `u`, `‖u‖_{H^t} ≤ ‖u‖_{H^s}`. In particular
`H^s ⊆ H^t` with norm-one inclusion, and (taking `t = 0`) `‖u‖_{L²} ≤ ‖u‖_{H^s}` for `s ≥ 0`. -/
theorem sobolevNorm_mono {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {s t : ℝ} (hts : t ≤ s) (u : 𝓢'(E, F)) :
    sobolevNorm t u ≤ sobolevNorm s u := by
  sorry

end SobolevL2
