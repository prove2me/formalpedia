-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_taylor
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.taylor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:59.674429+00:00
-- url     : https://prove2.me/theorems/e54598b6-6ebd-499e-a9bf-f98e4e464e32
-- title:
--   Jacobian Criterion Alt: taylor
-- statement:
--   The Jacobian Criterion Alt construction uses the taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L65-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L65-L80

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.taylor (p : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) :
    a - C (eval p a) - ∑ i, C (gradP p a i) * (X i - C (p i)) ∈ ptI p ^ 2 := by sorry
