-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_2_4
-- name    : SmoothedSimplex.TwoPhase.lemma_5_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:29:30.071741+00:00
-- url     : https://prove2.me/theorems/2513dd05-72d3-461b-ae3d-89688922b91d
-- title:
--   Lemma 5.2.4 (Changing α to α̃)
-- statement:
--   For $n>d\ge3$, fix a $d$-set $I$, positive relaxed-LP parameters $\kappa,M$, and a center matrix $\widetilde A$ with $s_{\min}(\widetilde A_I)\ge\kappa_0/2$. Perturb each column independently by an isotropic Gaussian of standard deviation $\tau_1=\kappa_0/(6d^3\sqrt{\ln n})$. Then
--   $$\mathbb E_{A,\alpha\in A_{1/d^2}}|\operatorname{Shadow}_{A_I\alpha,z}(a;y')|\le6\mathbb E_{A,\widetilde\alpha\in A_0}|\operatorname{Shadow}_{\widetilde A_I\widetilde\alpha,z}(a;y')|+1.$$
--   Here $y'$ is the LP′ right-hand side determined by $I,\kappa,M$. This replaces a data-dependent plane by one fixed before the final perturbation. **Formalization Note** Integrability is asserted as part of the result.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.2.4, printed p. 73, PDF p. 73

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.2.4 (Changing α to α̃), printed p. 73, PDF p. 73. The surrounding proof fixes τ₁=κ₀/(6d³√ln n); y′ is the relaxed right-hand side from T′ on p. 68. Formalization Note: `[n]` is `Fin n`; all expectations use the specified probability laws. -/
theorem lemma_5_2_4 {n d : ℕ} (hd : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (σ : ℝ) (hσ : 0 < σ)
    (I : DSet n d) (κ M : ℝ) (hκ : 0 < κ) (hM : 0 < M)
    (z : Point d)
    (hgood : kappaZero n d σ / 2 ≤ sMin c I.1) :
    MeasureTheory.Integrable (fun p =>
      (firstPhaseShadow p.1 I.1 (sampledCoefficients (d := d) I.1 p.2) κ M z : ℝ))
      ((gaussianFamily c (kappaZero n d σ /
        (6 * (d : ℝ)^3 * Real.sqrt (Real.log n)))).prod (exponentialWeights n)) ∧
    MeasureTheory.Integrable (fun p =>
      (((shadow p.1 (relaxedRhs (d := d) I.1 κ M)
        (∑ i ∈ I.1, (p.2 i / (∑ j ∈ I.1, p.2 j)) • c i) z).card) : ℝ))
      ((gaussianFamily c (kappaZero n d σ /
        (6 * (d : ℝ)^3 * Real.sqrt (Real.log n)))).prod (exponentialWeights n)) ∧
    (∫ p, (firstPhaseShadow p.1 I.1
      (sampledCoefficients (d := d) I.1 p.2) κ M z : ℝ)
      ∂((gaussianFamily c (kappaZero n d σ /
        (6 * (d : ℝ)^3 * Real.sqrt (Real.log n)))).prod (exponentialWeights n))) ≤
      6 * (∫ p, (((shadow p.1 (relaxedRhs (d := d) I.1 κ M)
        (∑ i ∈ I.1, (p.2 i / (∑ j ∈ I.1, p.2 j)) • c i) z).card) : ℝ)
        ∂((gaussianFamily c (kappaZero n d σ /
          (6 * (d : ℝ)^3 * Real.sqrt (Real.log n)))).prod (exponentialWeights n))) + 1 := by sorry

end SmoothedSimplex.TwoPhase
