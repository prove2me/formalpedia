-- Prove2me | Theorems.Thm_PI_KLW_conjK_spec
-- name    : PI.KLW.conjK_spec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:55.421963+00:00
-- url     : https://prove2.me/theorems/0f3d4d28-b6aa-430c-b5a9-7a89687d5796
-- title:
--   KLW: conj K spec
-- statement:
--   The KLW construction uses the conj K spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L38-L41

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K E : Type} [Field K] [Field E] [CharZero E] [Algebra K E]

theorem PI.KLW.conjK_spec (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') (k : K) :
    algebraMap K E (conjK cj h k) = cj (algebraMap K E k) := by sorry
