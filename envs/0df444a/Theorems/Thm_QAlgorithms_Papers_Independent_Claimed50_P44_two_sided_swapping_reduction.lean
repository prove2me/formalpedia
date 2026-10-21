-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_two_sided_swapping_reduction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.two_sided_swapping_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:11:25.308473+00:00
-- url     : https://prove2.me/theorems/3f075f57-cec4-406d-a84b-c0270d35230e
-- title:
--   Three alternatives attain the diagonal two-sided process optimum
-- statement:
--   Fix a physical standard-form centered two-mode Gaussian resource and the renormalized process score of the specified unity-gain protocol. Restrict preprocessing to independent diagonal Gaussian channels on Alice and Bob, with all nonnegative diagonal noises satisfying their local CP constraints. There exists an optimal strategy among the following alternatives: Alice acts and Bob does nothing; Bob acts and Alice does nothing; or both modes are replaced by vacuum. In particular,
--
--   $$\sup_{\text{all independent diagonal strategies}}\mathcal F=\max_{\text{three alternatives}}\mathcal F,$$
--
--   and a finite admissible strategy attains this common value. Replacing both modes by vacuum gives $\mathcal F=1$. Zero gains are included explicitly.
--
--   This is equality of optimal values and existence of a representative optimizer, not a classification of all optimizers or an unrestricted two-sided Gaussian optimality claim.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 6, §III, Eqs.(56)–(59)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF pp.5-6, Eqs.(56)-(59): equality of optimal values and an attained
optimum among the three alternatives, only in the independent diagonal class.
Zero gains are included. This does not classify every optimizer. -/
theorem two_sided_swapping_reduction (a b c1 c2 : ℝ)
    (hresource : PhysicalResource (standardCov a b c1 c2)) :
    let V := standardCov a b c1 c2
    ∃ best : DiagonalStrategy, ValidStrategy best ∧ ThreeAlternatives best ∧
      (∀ s : DiagonalStrategy, ValidStrategy s → strategyScore V s ≤ strategyScore V best) ∧
      sSup (strategyValues V false) = strategyScore V best ∧
      sSup (strategyValues V true) = strategyScore V best ∧
      processScore (resourceWigner (1 : JointMat) 0) = 1 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
