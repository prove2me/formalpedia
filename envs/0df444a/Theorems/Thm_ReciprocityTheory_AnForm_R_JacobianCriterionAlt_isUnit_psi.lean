-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_isUnit_psi
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.isUnit_psi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:18.468399+00:00
-- url     : https://prove2.me/theorems/a42eaf15-6345-5802-87eb-f1ca5b7f9d7c
-- title:
--   Jacobian Criterion Alt: is Unit psi
-- statement:
--   The Jacobian Criterion Alt construction uses the is Unit psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L127-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L127-L128

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.isUnit_psi {s : MvPolynomial (Fin n) ℂ} (hs : s ∉ ptI p) : IsUnit (psi p K s) := by sorry
