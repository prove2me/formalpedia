-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_evRing_psi
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.evRing_psi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:42.185286+00:00
-- url     : https://prove2.me/theorems/ab52244f-5a88-41e0-9371-f2c98731817f
-- title:
--   Jacobian Criterion Alt: ev Ring psi
-- statement:
--   The Jacobian Criterion Alt construction uses the ev Ring psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L140-L142

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.evRing_psi (hK : K ≤ ptI p) (a : MvPolynomial (Fin n) ℂ) :
    evRing K hK (psi p K a) = eval p a := by sorry
