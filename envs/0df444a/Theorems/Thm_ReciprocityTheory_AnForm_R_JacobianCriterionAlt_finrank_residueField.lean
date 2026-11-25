-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_finrank_residueField
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.finrank_residueField
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:43.86315+00:00
-- url     : https://prove2.me/theorems/856607dd-e8c2-4912-bf9e-52834a440344
-- title:
--   Jacobian Criterion Alt: finrank residue Field
-- statement:
--   The Jacobian Criterion Alt construction uses the finrank residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L127-L136

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
variable {n : ℕ} (p : Fin n → ℂ) (K : Ideal (MvPolynomial (Fin n) ℂ)) [IsLocalRing (locR K p)]

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.finrank_residueField : Module.finrank ℂ (ResidueField (locR K p)) = 1 := by sorry
