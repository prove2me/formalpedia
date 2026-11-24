-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_A_WpSh_rescale_C__e9f3bb5ac876
-- name    : P2M_Formalism_L2_Th1_A_WpSh_rescale_C__e9f3bb5ac876
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:56:03.08883+00:00
-- url     : https://prove2.me/theorems/1bbd4ba4-bfc5-450f-b8fe-d07bb70c1436
-- title:
--   P2 M Formalism L2 Th1 A Wp Sh rescale C  e9f3bb5ac876: P2 M Formalism L2 Th1 A Wp Sh rescale C  e9f3bb5ac876
-- statement:
--   The P2 M Formalism L2 Th1 A Wp Sh rescale C  e9f3bb5ac876 construction uses the P2 M Formalism L2 Th1 A Wp Sh rescale C  e9f3bb5ac876 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/WpShape.lean#L104-L107

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]

theorem P2M_Formalism_L2_Th1_A_WpSh_rescale_C__e9f3bb5ac876 (a c : K) : rescale a (C c) = C c := by sorry

alias «Formalism».«L2».«Th1».«A».«WpSh».«rescale_C'» := P2M_Formalism_L2_Th1_A_WpSh_rescale_C__e9f3bb5ac876
