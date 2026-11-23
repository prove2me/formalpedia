-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_toCot_psi
-- name    : ReciprocityTheory.AnForm.R.JacobianCriterionAlt.toCot_psi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:21.273389+00:00
-- url     : https://prove2.me/theorems/899a23db-511b-439e-b015-b5c6fcd85338
-- title:
--   Jacobian Criterion Alt: to Cot psi
-- statement:
--   The Jacobian Criterion Alt construction uses the to Cot psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L26-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L26-L50

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
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
variable {n : ℕ} (p : Fin n → ℂ) (K : Ideal (MvPolynomial (Fin n) ℂ)) [IsLocalRing (locR K p)]

theorem ReciprocityTheory.AnForm.R.JacobianCriterionAlt.toCot_psi {a : MvPolynomial (Fin n) ℂ} (ha : a ∈ ptI p)
    (hm : psi p K a ∈ maximalIdeal (locR K p)) :
    (maximalIdeal (locR K p)).toCotangent ⟨psi p K a, hm⟩ = Phi p K (gradP p a) := by sorry
