-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_two_sided_noise_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.two_sided_noise_optimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:10:57.431543+00:00
-- url     : https://prove2.me/theorems/b6d020bc-bf1e-4987-b1c8-219a51b13a64
-- title:
--   Independent diagonal noise optimization with all boundary regimes
-- statement:
--   Let the resource be a finite physical standard-form Gaussian state, and let $D=\operatorname{diag}(d_1,d_2)$ be a physical pure-input covariance or the formal zero process matrix. Fix independent diagonal gains $(u,v)$ for Alice and $(x,y)$ for Bob. Write $\alpha=2d_1+au^2+2c_1ux+bx^2$ and $\beta=2d_2+av^2-2c_2vy+by^2$, which are nonnegative. Among four nonnegative noises satisfying $g_{A1}g_{A2}\ge(1-uv)^2$ and $g_{B1}g_{B2}\ge(1-xy)^2$, the raw determinant has infimum
--
--   $$\inf (\alpha+g_{A1}+g_{B1})(\beta+g_{A2}+g_{B2})=(|1-uv|+|1-xy|+\sqrt{\alpha\beta})^2.$$
--
--   The lower bound holds for every feasible noise, and every positive tolerance admits a feasible noise within that tolerance. If $\alpha,\beta>0$, the infimum is attained at $g_{A1}=|1-uv|\sqrt{\alpha/\beta}$, $g_{A2}=|1-uv|\sqrt{\beta/\alpha}$, and the analogous Bob entries. If $\alpha=\beta=0$, all four noises equal to one attain the value $4$. If exactly one of $\alpha,\beta$ is zero, the infimum is $4$ and every feasible finite-noise determinant is strictly larger than $4$.
--
--   This corrects the printed attainment assertion at degenerate process objectives while retaining the full source domain.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 5, §III, Eqs.(49)–(55), corrected boundary

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.5, Eqs.(49)-(55), corrected boundary omission (trap 30).
Printed: a global minimum is attained by the divided expressions (54).
Changed: raw determinant and three explicit attainment regimes. Why: when
exactly one base variance is zero (possible only for D=0), the value 4 is an
unattained infimum; substituting Lean's division-by-zero value would be false. -/
theorem two_sided_noise_optimum (a b c1 c2 d1 d2 u v x y : ℝ)
    (hresource : PhysicalResource (standardCov a b c1 c2))
    (hD : InputOrProcess (!![d1, 0; 0, d2] : QuadratureMatrix)) :
    let al := 2 * d1 + a * u ^ 2 + 2 * c1 * u * x + b * x ^ 2
    let be := 2 * d2 + a * v ^ 2 - 2 * c2 * v * y + b * y ^ 2
    let val := twoNoiseValue al be u v x y
    0 ≤ al ∧ 0 ≤ be ∧
    (∀ g : Noises, FeasibleNoises u v x y g → val ≤ rawTwoDet al be g) ∧
    (∀ eps : ℝ, 0 < eps → ∃ g : Noises,
      FeasibleNoises u v x y g ∧ rawTwoDet al be g < val + eps) ∧
    (0 < al → 0 < be →
      let g : Noises := ![|1 - u * v| * Real.sqrt (al / be),
        |1 - u * v| * Real.sqrt (be / al), |1 - x * y| * Real.sqrt (al / be),
        |1 - x * y| * Real.sqrt (be / al)]
      FeasibleNoises u v x y g ∧ rawTwoDet al be g = val) ∧
    (al = 0 → be = 0 → val = 4 ∧ FeasibleNoises u v x y ![1, 1, 1, 1] ∧
      rawTwoDet al be ![1, 1, 1, 1] = val) ∧
    ((al = 0 ∧ 0 < be) ∨ (0 < al ∧ be = 0) →
      val = 4 ∧ ∀ g : Noises, FeasibleNoises u v x y g →
        val < rawTwoDet al be g) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
