-- Prove2me | Theorems.Thm_PI_KLW_natCast_mul_mem
-- name    : PI.KLW.natCast_mul_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:33:31.655778+00:00
-- url     : https://prove2.me/theorems/d00b4ae1-cc4f-597f-96c2-6630e2921aaa
-- title:
--   KLW: nat Cast mul mem
-- statement:
--   The KLW construction uses the nat Cast mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairingFactorsThroughPeriods.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairingFactorsThroughPeriods.lean#L46-L49

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

theorem PI.KLW.natCast_mul_mem (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (q : ℕ) {z : E}
    (hz : z ∈ I) : (q : E) * z ∈ I := by sorry
