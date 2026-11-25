-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_isNoetherianRing_locPt
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.isNoetherianRing_locPt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:40.547796+00:00
-- url     : https://prove2.me/theorems/649e443a-d5d5-4308-b51e-d747777dc601
-- title:
--   Jacobian Criterion Alt: is Noetherian Ring loc Pt
-- statement:
--   The Jacobian Criterion Alt construction uses the is Noetherian Ring loc Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L153-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L153-L154

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.isNoetherianRing_locPt (p : Fin n → ℂ) : IsNoetherianRing (localization₂ p) := by sorry
