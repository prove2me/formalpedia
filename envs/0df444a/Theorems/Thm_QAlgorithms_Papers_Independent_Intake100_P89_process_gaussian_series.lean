-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_process_gaussian_series
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.process_gaussian_series
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:54:38.504845+00:00
-- url     : https://prove2.me/theorems/a7ee330f-dc70-428a-90f0-577c9453aa62
-- title:
--   §4, unnumbered L2 Gaussian-process series
-- statement:
--   Let $W_t=\sum_j\mu_jZ_j\phi_j(t)$ in $L^2(P)$ for every $t$, where $Z_j$ are iid standard normals. Then
--   $$K(s,t)=\sum_j\mu_j^2\phi_j(s)\phi_j(t).$$
--   For the RKHS conclusion assume the weighted coefficient uniqueness of Theorem 4.1 after deleting zero-variance directions. Then its elements are exactly $f_w(t)=\sum_jw_j\phi_j(t)$, where $w_j=0$ if $\mu_j=0$ and $\sum_jw_j^2/\mu_j^2<\infty$, and
--   $$\langle f_v,f_w\rangle_H=\sum_{j:\mu_j\ne0}\frac{v_jw_j}{\mu_j^2}.$$
--   Zero directions are forced to have zero deterministic coefficients, and the covariance conclusion is independent of the uniqueness clause.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 12, §4, unnumbered L2 Gaussian-process series

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section MoreResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- §4, unnumbered L2 Gaussian-process series, arXiv:0805.3252v1, PDF p.12.
The covariance assertion precedes the conditional uniqueness hypothesis. Zero-weight indices are removed before division. L² convergence is coordinatewise, with no Banach or uniform-path convergence assumption. -/
theorem process_gaussian_series
{T : Type v} (W : T → Omega → ℝ) (hW : CenteredProcess P W)
    (mu : ℕ → ℝ) (Z : ℕ → Omega → ℝ) (hZ : StandardNormals P Z)
    (phi : ℕ → T → ℝ)
    (hseries : ∀ t, Tendsto
      (fun n => ∑ j ∈ Finset.range n, (mu j * phi j t) • toL2 P (Z j))
      atTop (𝓝 (toL2 P (W t)))) :
    (∀ s t, HasSum (fun j => (mu j) ^ 2 * phi j s * phi j t) (processCovariance P W s t)) ∧
    (∀ t, Summable (fun j => (mu j) ^ 2 * (phi j t) ^ 2)) ∧
    let admissible := fun w : ℕ → ℝ =>
      (∀ j, mu j = 0 → w j = 0) ∧
      Summable (fun j => if mu j = 0 then 0 else (w j) ^ 2 / (mu j) ^ 2)
    (∀ w, admissible w → (∀ t, (∑' j, w j * phi j t) = 0) → ∀ j, w j = 0) →
      (∀ w, admissible w → ∀ t, Summable (fun j => |w j * phi j t|)) ∧
      processRKHS P W = {f | ∃ w, admissible w ∧ f = fun t => ∑' j, w j * phi j t} ∧
      ∀ v w, admissible v → admissible w →
        processInner P W (fun t => ∑' j, v j * phi j t)
          (fun t => ∑' j, w j * phi j t) =
            ∑' j, if mu j = 0 then 0 else v j * w j / (mu j) ^ 2 := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
