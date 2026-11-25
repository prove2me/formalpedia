-- Prove2me | Theorems.Thm_P2M_PI_VolSemiDirect_W_mem__b6017dbedb26
-- name    : P2M_PI_VolSemiDirect_W_mem__b6017dbedb26
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:01:42.906813+00:00
-- url     : https://prove2.me/theorems/b84e72fc-6ede-5d90-baea-0005b22e7a5a
-- title:
--   P2 M PI Vol Semi Direct W mem  b6017dbedb26: P2 M PI Vol Semi Direct W mem  b6017dbedb26
-- statement:
--   The P2 M PI Vol Semi Direct W mem  b6017dbedb26 construction uses the P2 M PI Vol Semi Direct W mem  b6017dbedb26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/VolumeQuotientHolds.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/VolumeQuotientHolds.lean#L34-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_VolumeQuotientHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open MeasureTheory

theorem P2M_PI_VolSemiDirect_W_mem__b6017dbedb26 {X : Type} [Group X] {Γ K : Subgroup X} (γ : ratG Γ K) : ((γ : K) : X) ∈ Γ := by sorry

alias «PI».«VolSemiDirect».«W».«memΓ» := P2M_PI_VolSemiDirect_W_mem__b6017dbedb26
