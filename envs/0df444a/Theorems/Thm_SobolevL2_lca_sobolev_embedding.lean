-- Prove2me | Theorems.Thm_SobolevL2_lca_sobolev_embedding
-- name    : SobolevL2.lca_sobolev_embedding
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:01:04.046645+00:00
-- url     : https://prove2.me/theorems/5d37fb3c-1e21-4c42-a664-8d29a12d8e6b
-- title:
--   Sobolev embedding on locally compact abelian groups: if $(1+w^2)^{-s/2}\in L^1(\widehat G)$, then $H^s_w(G)\hookrightarrow C_0(G)$ boundedly and injectively
-- statement:
--   **Sobolev embedding theorem for Sobolev spaces on locally compact abelian groups.** Let $G$ be a Hausdorff locally compact abelian group, $\widehat G$ its Pontryagin dual (continuous homomorphisms $\chi:G\to\mathbb T$, compact-open topology) and $\nu$ a Haar measure on $\widehat G$, regular in the sense of Radon measures (for instance the Plancherel measure of a Haar measure on $G$). Let $w:\widehat G\to[0,\infty)$ be a *Sobolev weight*: $w$ is continuous and there is $C_w>0$ with
--   $$w(\chi\chi')\le C_w\big(w(\chi)+w(\chi')\big)\qquad(\chi,\chi'\in\widehat G).$$
--   For $s\in\mathbb R$ the Sobolev space $H^s_w(G)$ is, on the Fourier side, the weighted space $L^2\big(\widehat G,(1+w^2)^{s/2}\nu\big)$, with norm
--   $$\|u\|_{H^s_w}=\Big(\int_{\widehat G}|u(\chi)|^2\,(1+w(\chi)^2)^{s/2}\,d\nu(\chi)\Big)^{1/2}.$$
--   Assume $s\ge0$ and $(1+w^2)^{-s/2}\in L^1(\widehat G,\nu)$. Then there is a constant $C>0$ such that for every $u\in H^s_w(G)$:
--   1. $u\in L^1(\widehat G,\nu)$, so the inverse Fourier transform $\check u(x)=\int_{\widehat G}u(\chi)\,\chi(x)\,d\nu(\chi)$ is defined for every $x\in G$;
--   2. $\check u$ is continuous on $G$ and vanishes at infinity, $\check u\in C_0(G)$;
--   3. $\sup_{x\in G}|\check u(x)|\le C\,\|u\|_{H^s_w}$;
--   4. if $\check u\equiv0$ then $u=0$ $\nu$-almost everywhere.
--
--   Hence $u\mapsto\check u$ is a bounded injective linear map $H^s_w(G)\hookrightarrow C_0(G)$. When $\nu$ is the Plancherel measure, $\check u$ is the continuous representative of the element of $L^2(G)$ whose Plancherel transform is $u$, so every element of $H^s_w(G)$ is represented by a unique function in $C_0(G)$. One may take $C=\|(1+w^2)^{-s/2}\|_{L^1(\nu)}^{1/2}$ (Cauchy–Schwarz). For $G=\mathbb R^n$ and $w(\xi)=|\xi|$ the integrability condition is $s>n$ in the source's normalization, i.e. the classical condition "order $>n/2$".
--
--   This is Proposition 9.1.1.3(3) of the source ((9.1.1.7)–(9.1.1.8)), the Sobolev embedding for the Sobolev spaces of [GR]; the source proves it with [Ru, Thm. 1.2.4(d)] (the bound of the inverse transform of an integrable function by its $L^1$ norm) and [DE, Thm. 3.2.1] (its vanishing at infinity, and injectivity).
--
--   **Formalization Note.** The weighted Fourier-side model $L^2(\widehat G,(1+w^2)^{s/2}\nu)$ is used as the definition of $H^s_w(G)$, as in the proof of Lemma 9.1.1.2 of the source (erratum I93 of the riemann-masullo formalization, https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md: the source's (9.1.1.3) mixes test functions on $\widehat G$ with a Fourier transform). Membership is `MemLp u 2 (ν.withDensity (1 + w²)^{s/2})` and the norm is the corresponding `eLpNorm`. $\widehat G$ is Mathlib's `PontryaginDual G` with its Borel σ-algebra and a Haar measure `ν` which is `Regular` (Mathlib's `IsHaarMeasure` alone does not impose the Radon regularity that the classical notion of Haar measure includes; on non-σ-compact groups this matters); $\chi(x)$ is the value in `Circle ⊆ ℂ`. "Vanishing at infinity" is convergence to $0$ along the cocompact filter of $G$. The sup bound is stated pointwise in $[0,\infty]$ with a constant $C$ chosen before $u$. The statement is made for an arbitrary Haar measure $\nu$ (all Haar measures are proportional, so this is equivalent to the case of the Plancherel measure); the identification of $\check u$ with the $L^2(G)$-class of the inverse Plancherel transform is the Plancherel theorem and is not restated. The quasi-subadditivity of $w$ is part of the source's notion of Sobolev weight and is kept as a hypothesis.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 397, Proposition 9.1.1.3(3) (Sobolev Embedding), (9.1.1.7)–(9.1.1.8), with Definition 9.1.1.1 and Lemma 9.1.1.2 on p. 396; classical reference: P. Górka and E. G. Reyes, Sobolev spaces on locally compact abelian groups, arXiv:1208.3053v1 (2012), §§1–2 (Sobolev spaces on locally compact abelian groups), as cited by the paper at Definition 9.1.1.1; the paper's proof uses W. Rudin, Fourier Analysis on Groups, Wiley-Interscience, 1962, Thm. 1.2.4(d), and A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Thm. 3.2.1

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace SobolevL2

/-- Sobolev embedding on a Hausdorff locally compact abelian group `G`, on the Fourier side.
`ν` is a (regular) Haar measure on the dual group, `w` a Sobolev weight on the dual group, `s ≥ 0`, and the
reciprocal weight `(1 + w²)^{-s/2}` is `ν`-integrable. Then there is `C > 0` such that every `u` in
the weighted space `L²(Ĝ, (1 + w²)^{s/2} ν)` (the Fourier-side model of `H^s_w(G)`) is
`ν`-integrable, its inverse Fourier transform `x ↦ ∫ u(χ) χ(x) dν(χ)` is a continuous function
on `G` vanishing at infinity with sup norm at most `C ‖u‖_{H^s_w}`, and it vanishes identically
only if `u = 0` almost everywhere. -/
theorem lca_sobolev_embedding {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]
    (w : PontryaginDual G → ℝ≥0) (hw_cont : Continuous w)
    (hw_sub : ∃ C : ℝ≥0, 0 < C ∧ ∀ χ χ' : PontryaginDual G, w (χ * χ') ≤ C * (w χ + w χ'))
    (s : ℝ) (hs : 0 ≤ s)
    (hint : Integrable (fun χ => (1 + (w χ : ℝ) ^ 2) ^ (-s / 2)) ν) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ u : PontryaginDual G → ℂ,
      MemLp u 2 (ν.withDensity fun χ => ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (s / 2))) →
      Integrable u ν ∧
      Continuous (fun x : G => ∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν) ∧
      Tendsto (fun x : G => ∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν) (cocompact G) (𝓝 0) ∧
      (∀ x : G, ‖∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν‖ₑ ≤
        C * eLpNorm u 2 (ν.withDensity fun χ => ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (s / 2)))) ∧
      ((∀ x : G, ∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν = 0) → u =ᵐ[ν] 0) := by
  sorry

end SobolevL2
