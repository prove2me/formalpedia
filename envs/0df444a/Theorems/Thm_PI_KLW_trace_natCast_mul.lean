-- Prove2me | Theorems.Thm_PI_KLW_trace_natCast_mul
-- name    : PI.KLW.trace_natCast_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:09.600806+00:00
-- url     : https://prove2.me/theorems/75bc24d8-9ba8-5c5b-a1b2-e5288262af4b
-- title:
--   KLW: trace nat Cast mul
-- statement:
--   The KLW construction uses the trace nat Cast mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean#L49-L54

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

theorem PI.KLW.trace_natCast_mul (cj : E ≃ₐ[ℚ] E) (s t : ℕ) (x y : E) :
    Algebra.trace K E (((s : E) * x) * cj ((t : E) * y)) =
      ((s * t : ℕ) : K) * Algebra.trace K E (x * cj y) := by sorry
