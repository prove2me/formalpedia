-- Prove2me | Theorems.Thm_PI_KLW_trace_mul_natCast
-- name    : PI.KLW.trace_mul_natCast
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:33:08.447916+00:00
-- url     : https://prove2.me/theorems/165ab524-9a72-4490-adf5-5a7363eee683
-- title:
--   KLW: trace mul nat Cast
-- statement:
--   The KLW construction uses the trace mul nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairingFactorsThroughPeriods.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairingFactorsThroughPeriods.lean#L11-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods
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
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem PI.KLW.trace_mul_natCast (cj : E ≃ₐ[ℚ] E) (s : ℕ) (z y : E) :
    Algebra.trace K E (z * cj ((s : E) * y)) = (s : K) * Algebra.trace K E (z * cj y) := by sorry
