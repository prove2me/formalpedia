-- Prove2me | Theorems.Thm_PI_KLW_exists_ne_zero_mem
-- name    : PI.KLW.exists_ne_zero_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:15.905144+00:00
-- url     : https://prove2.me/theorems/3931e9a8-0b9d-581e-90e0-795d670f72de
-- title:
--   KLW: exists ne zero mem
-- statement:
--   The KLW construction uses the exists ne zero mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairingFactorsThroughPeriods.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairingFactorsThroughPeriods.lean#L17-L23

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

theorem PI.KLW.exists_ne_zero_mem (cj : E ≃ₐ[ℚ] E) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hI : PI.KerIso.SelfDualI K cj I) : ∃ y0 ∈ I, y0 ≠ 0 := by sorry
