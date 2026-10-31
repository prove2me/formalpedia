-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_covariance_series_rkhs
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.covariance_series_rkhs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:40:55.380785+00:00
-- url     : https://prove2.me/theorems/c277d4d7-9ac7-40ca-a6b5-52dac95c8522
-- title:
--   Theorem 4.1: covariance-series RKHS
-- statement:
--   Let $W$ be a centered Gaussian process on an arbitrary set $T$. Suppose $\lambda_j>0$ and
--   $$K(s,t)=\sum_j\lambda_j\phi_j(s)\phi_j(t),\qquad\sum_j\lambda_j\phi_j(t)^2<\infty.$$
--   Assume strong coefficient uniqueness: every sequence with $\sum_jw_j^2/\lambda_j<\infty$ that synthesizes the zero function is zero. Then the RKHS is exactly the functions $f_w(t)=\sum_jw_j\phi_j(t)$ with this weighted square summability, these series converge absolutely pointwise, and
--   $$\langle f_v,f_w\rangle_H=\sum_j\frac{v_jw_j}{\lambda_j}.$$
--   No orthogonality of the functions, compactness of $T$, or reference measure is required.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 10, Theorem 4.1: covariance-series RKHS

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

/-- Theorem 4.1: covariance-series RKHS, arXiv:0805.3252v1, PDF p.10.
Strong weighted infinite-series uniqueness is a hypothesis, not just finite linear independence. All denominators are strictly positive. -/
theorem covariance_series_rkhs
{T : Type v} (W : T → Omega → ℝ) (hW : CenteredProcess P W)
    (lam : ℕ → ℝ) (phi : ℕ → T → ℝ) (hlam : ∀ j, 0 < lam j)
    (hdiag : ∀ t, Summable (fun j => lam j * (phi j t) ^ 2))
    (hcov : ∀ s t, HasSum (fun j => lam j * phi j s * phi j t) (processCovariance P W s t))
    (hunique : ∀ w : ℕ → ℝ, Summable (fun j => (w j) ^ 2 / lam j) →
      (∀ t, (∑' j, w j * phi j t) = 0) → ∀ j, w j = 0) :
    (∀ w : ℕ → ℝ, Summable (fun j => (w j) ^ 2 / lam j) →
      ∀ t, Summable (fun j => |w j * phi j t|)) ∧
    processRKHS P W = {f | ∃ w : ℕ → ℝ,
      Summable (fun j => (w j) ^ 2 / lam j) ∧ f = fun t => ∑' j, w j * phi j t} ∧
    ∀ v w : ℕ → ℝ,
      Summable (fun j => (v j) ^ 2 / lam j) →
      Summable (fun j => (w j) ^ 2 / lam j) →
      processInner P W (fun t => ∑' j, v j * phi j t)
        (fun t => ∑' j, w j * phi j t) = ∑' j, v j * w j / lam j := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
