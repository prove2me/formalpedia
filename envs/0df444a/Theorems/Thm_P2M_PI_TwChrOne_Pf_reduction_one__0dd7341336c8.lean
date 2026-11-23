-- Prove2me | Theorems.Thm_P2M_PI_TwChrOne_Pf_reduction_one__0dd7341336c8
-- name    : P2M_PI_TwChrOne_Pf_reduction_one__0dd7341336c8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:05.458442+00:00
-- url     : https://prove2.me/theorems/7628104f-bb49-41cd-831f-9d04b5370462
-- title:
--   P2 M PI Tw Chr One Pf reduction one  0dd7341336c8: P2 M PI Tw Chr One Pf reduction one  0dd7341336c8
-- statement:
--   The P2 M PI Tw Chr One Pf reduction one  0dd7341336c8 construction uses the P2 M PI Tw Chr One Pf reduction one  0dd7341336c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L101-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L101-L101

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

theorem P2M_PI_TwChrOne_Pf_reduction_one__0dd7341336c8 : redP P (1 : E) = 1 := by sorry

alias «PI».«TwChrOne».«Pf».«reduction_one₂» := P2M_PI_TwChrOne_Pf_reduction_one__0dd7341336c8
