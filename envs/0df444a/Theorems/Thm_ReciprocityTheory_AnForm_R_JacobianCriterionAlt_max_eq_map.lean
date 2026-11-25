-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_max_eq_map
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.max_eq_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:30.818843+00:00
-- url     : https://prove2.me/theorems/27af5170-9157-49a7-888a-27dceb4939b4
-- title:
--   Jacobian Criterion Alt: max eq map
-- statement:
--   The Jacobian Criterion Alt construction uses the max eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L165-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L165-L177

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
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
variable {p : Fin n → ℂ} (K : Ideal (MvPolynomial (Fin n) ℂ))

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.max_eq_map [IsLocalRing (locR K p)] (hK : K ≤ ptI p) :
    maximalIdeal (locR K p) = (ptI p).map (psi p K) := by sorry
