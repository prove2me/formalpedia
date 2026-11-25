-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_psi_mem_sq
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.psi_mem_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:24.167078+00:00
-- url     : https://prove2.me/theorems/8e0df695-22d1-5a61-b9e4-1544a5b8e969
-- title:
--   Jacobian Criterion Alt: psi mem sq
-- statement:
--   The Jacobian Criterion Alt construction uses the psi mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L179-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L179-L182

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.psi_mem_sq [IsLocalRing (locR K p)] (hK : K ≤ ptI p) {a : MvPolynomial (Fin n) ℂ}
    (ha : a ∈ ptI p ^ 2) : psi p K a ∈ maximalIdeal (locR K p) ^ 2 := by sorry
