-- Prove2me | Theorems.Thm_P2M_PI_TwChrOne_Pf_reduction_sum__8241acdd8e6b
-- name    : P2M_PI_TwChrOne_Pf_reduction_sum__8241acdd8e6b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:25.825047+00:00
-- url     : https://prove2.me/theorems/7e2e0cb6-d2a0-401e-b729-95f8218bc0ca
-- title:
--   P2 M PI Tw Chr One Pf reduction sum  8241acdd8e6b: P2 M PI Tw Chr One Pf reduction sum  8241acdd8e6b
-- statement:
--   The P2 M PI Tw Chr One Pf reduction sum  8241acdd8e6b construction uses the P2 M PI Tw Chr One Pf reduction sum  8241acdd8e6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L108-L112

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem P2M_PI_TwChrOne_Pf_reduction_sum__8241acdd8e6b {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by sorry

alias «PI».«TwChrOne».«Pf».«reduction_sum₂» := P2M_PI_TwChrOne_Pf_reduction_sum__8241acdd8e6b
