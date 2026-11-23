-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_sum
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:25.997393+00:00
-- url     : https://prove2.me/theorems/92d06a51-350b-44c7-8a72-0d5ec2cd95bf
-- title:
--   Jacobian Criterion Alt: grad sum
-- statement:
--   The Jacobian Criterion Alt construction uses the grad sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean#L44-L46

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

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_sum (p : Fin n → ℂ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℂ) :
    gradP p (∑ i ∈ s, f i) = ∑ i ∈ s, gradP p (f i) := by sorry
