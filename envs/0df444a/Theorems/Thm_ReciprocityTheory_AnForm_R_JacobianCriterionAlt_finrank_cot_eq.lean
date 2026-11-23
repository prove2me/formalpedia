-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_finrank_cot_eq
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.finrank_cot_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:11.950924+00:00
-- url     : https://prove2.me/theorems/71ef67e7-f284-4ba0-a117-2678d551c790
-- title:
--   Jacobian Criterion Alt: finrank cot eq
-- statement:
--   The Jacobian Criterion Alt construction uses the finrank cot eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L138-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L138-L147

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.finrank_cot_eq :
    Module.finrank (ResidueField (locR K p)) (CotangentSpace (locR K p))
      + Module.finrank ℂ (jacS K p) = n := by sorry
