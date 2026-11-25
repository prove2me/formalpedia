-- Prove2me | Theorems.Thm_PI_FJMX_pderiv_mem_supported
-- name    : PI.FJMX.pderiv_mem_supported
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:12.551317+00:00
-- url     : https://prove2.me/theorems/8404b71c-6c7d-44c3-a23a-417634279e58
-- title:
--   FJMX: pderiv mem supported
-- statement:
--   The FJMX construction uses the pderiv mem supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L150-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean#L150-L162

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R : Type*} [CommRing R] {σ : Type*}

theorem PI.FJMX.pderiv_mem_supported {S : Set σ} {f : MvPolynomial σ R} (hf : f ∈ supported R S)
    (v : σ) : pderiv v f ∈ supported R S := by sorry
