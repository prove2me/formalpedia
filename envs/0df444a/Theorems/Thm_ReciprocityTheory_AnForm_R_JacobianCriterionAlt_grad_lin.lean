-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_lin
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:21.873361+00:00
-- url     : https://prove2.me/theorems/f2af0414-30a2-45d7-8947-81143913b44d
-- title:
--   Jacobian Criterion Alt: grad lin
-- statement:
--   The Jacobian Criterion Alt construction uses the grad lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L48-L49

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_lin (p : Fin n → ℂ) (i : Fin n) : gradP p (X i - C (p i)) = Pi.single i 1 := by sorry
