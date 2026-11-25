-- Prove2me | Theorems.Thm_P2M_PI_VolStabW_exOmT_of_steps__237885209129
-- name    : P2M_PI_VolStabW_exOmT_of_steps__237885209129
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:02:20.729637+00:00
-- url     : https://prove2.me/theorems/1584f0d9-8034-5b81-bd6b-5db774fafd55
-- title:
--   P2 M PI Vol Stab W ex Om T of steps  237885209129: P2 M PI Vol Stab W ex Om T of steps  237885209129
-- statement:
--   The P2 M PI Vol Stab W ex Om T of steps  237885209129 construction uses the P2 M PI Vol Stab W ex Om T of steps  237885209129 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExOmTOfSteps.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ExOmTOfSteps.lean#L19-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocExOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExOmTOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem P2M_PI_VolStabW_exOmT_of_steps__237885209129 (hI : FibInfEx) (hV : FibVEx) (hU : SdUniq) (hDI : DensFibInf)
    (hDV : DensFibV) (hR : RestrProd) : ExOmT := by sorry

alias «PI».«VolStabW».«exOmT_of_steps'» := P2M_PI_VolStabW_exOmT_of_steps__237885209129
