-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_mul_mem_of_algebraMap_mem
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.exists_mul_mem_of_algebraMap_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:30.417247+00:00
-- url     : https://prove2.me/theorems/c1eebdb3-b696-41c4-9bf0-e6afc0b33577
-- title:
--   Jacobian Criterion Alt: exists mul mem of algebra Map mem
-- statement:
--   The Jacobian Criterion Alt construction uses the exists mul mem of algebra Map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L99-L109

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.exists_mul_mem_of_algebraMap_mem (p : Fin n → ℂ) {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {a : MvPolynomial (Fin n) ℂ}
    (h : algebraMap _ (localization₂ p) a ∈ I.map (algebraMap _ (localization₂ p))) :
    ∃ s, s ∉ ptI p ∧ s * a ∈ I := by sorry
