-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_psi_mem_max_iff
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.psi_mem_max_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:37.072562+00:00
-- url     : https://prove2.me/theorems/6f2079a7-c340-447c-a173-1e6ab4699542
-- title:
--   Jacobian Criterion Alt: psi mem max iff
-- statement:
--   The Jacobian Criterion Alt construction uses the psi mem max iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L150-L152

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.psi_mem_max_iff [IsLocalRing (locR K p)] (hK : K ≤ ptI p)
    (a : MvPolynomial (Fin n) ℂ) : psi p K a ∈ maximalIdeal (locR K p) ↔ a ∈ ptI p := by sorry
