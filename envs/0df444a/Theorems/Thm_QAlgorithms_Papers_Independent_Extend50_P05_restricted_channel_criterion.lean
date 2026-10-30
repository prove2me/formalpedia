-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_restricted_channel_criterion
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.restricted_channel_criterion
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:25:23.707616+00:00
-- url     : https://prove2.me/theorems/175f077e-ec4e-4498-bc17-fb3b015a6794
-- title:
--   Exact restricted CPTP criterion
-- statement:
--   Let $d\ge2$, $\alpha,\beta\in\mathbb R$ and $\gamma\in\mathbb C$. In the input-first three-qudit basis let $u_i=\sum_a|a,a,i\rangle$, $v_i=\sum_a|a,i,a\rangle$, $A=\sum_i|u_i\rangle\langle u_i|$, $B=\sum_i|v_i\rangle\langle v_i|$, and $R=\sum_i|v_i\rangle\langle u_i|$. The operator $C=\alpha A+\beta B+\gamma R+\overline\gamma R^*$ is the unnormalized Choi matrix of a complex-linear CPTP map if and only if
--
--   $$
--   d(\alpha+\beta)+2\operatorname{Re}\gamma=1,
--   \qquad |\gamma|^2\le\alpha\beta.
--   $$
--
--   Positivity and nonnegativity of $\alpha,\beta$ are not assumed as additional hypotheses.
--
--   This is the exact scalar test for the four-operator restricted family.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 9, Unnumbered restricted CPTP criterion, Eq. (7)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.9, Eq.(7): an iff for an actual CPTP Choi matrix; positivity is a conclusion.
The preceding displayed determinant omits a positive factor d^2-1, which leaves Eq.(7) unchanged. -/
theorem restricted_channel_criterion (d : ℕ) (hd : 2 ≤ d)
    (alpha beta : ℝ) (gamma : ℂ) :
    (∃ T : Superop (Fin d) (CloningOutputs d 2),
      IsChannel T ∧ choi T = restrictedChoi d alpha beta gamma) ↔
      (d : ℝ) * (alpha + beta) + 2 * gamma.re = 1 ∧
      Complex.normSq gamma ≤ alpha * beta := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
