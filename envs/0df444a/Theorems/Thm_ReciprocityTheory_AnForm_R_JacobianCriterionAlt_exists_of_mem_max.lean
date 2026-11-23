-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_of_mem_max
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.exists_of_mem_max
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:20.275499+00:00
-- url     : https://prove2.me/theorems/e4afe9d1-9be0-41e9-9576-e309f1afb8dd
-- title:
--   Jacobian Criterion Alt: exists of mem max
-- statement:
--   The Jacobian Criterion Alt construction uses the exists of mem max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L154-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L154-L163

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.exists_of_mem_max [IsLocalRing (locR K p)] (hK : K ≤ ptI p) {m : locR K p}
    (hm : m ∈ maximalIdeal (locR K p)) :
    ∃ a s, a ∈ ptI p ∧ s ∉ ptI p ∧ m * psi p K s = psi p K a := by sorry
