-- Prove2me | Theorems.Thm_PI_FJMX_derSum_apply
-- name    : PI.FJMX.derSum_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:01.117053+00:00
-- url     : https://prove2.me/theorems/870c25ed-8e0c-4624-8dcb-870fa80d4960
-- title:
--   FJMX: der Sum apply
-- statement:
--   The FJMX construction uses the der Sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L78-L81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m n : ℕ}

theorem PI.FJMX.derSum_apply {ι : Type*} (t : Finset ι) (D : ι → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (f : MvPolynomial σ ℂ) : (∑ c ∈ t, D c) f = ∑ c ∈ t, D c f := by sorry
