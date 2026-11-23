-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_mul
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:50:10.648852+00:00
-- url     : https://prove2.me/theorems/25475e5d-696d-4e6f-bd66-b23c6b021924
-- title:
--   Jacobian Criterion Alt: grad mul
-- statement:
--   The Jacobian Criterion Alt construction uses the grad mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L37-L39

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_mul (p : Fin n → ℂ) (x y : MvPolynomial (Fin n) ℂ) :
    gradP p (x * y) = eval p x • gradP p y + eval p y • gradP p x := by sorry
