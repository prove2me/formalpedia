-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_A_More_map_g__846035df1560
-- name    : P2M_Formalism_L2_Th1_A_More_map_g__846035df1560
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:37:35.682092+00:00
-- url     : https://prove2.me/theorems/39b62b2e-d44d-4d89-a4c1-f7f2e858667b
-- title:
--   P2 M Formalism L2 Th1 A More map g  846035df1560: P2 M Formalism L2 Th1 A More map g  846035df1560
-- statement:
--   The P2 M Formalism L2 Th1 A More map g  846035df1560 construction uses the P2 M Formalism L2 Th1 A More map g  846035df1560 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L185-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L185-L186

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open More
open Formalism.L2.Th1.A.More
variable {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L)

theorem P2M_Formalism_L2_Th1_A_More_map_g__846035df1560 (W : WeierstrassCurve K) : φ (g₂ W) = g₂ (W.map φ) := by sorry

alias «Formalism».«L2».«Th1».«A».«More».«map_g₂» := P2M_Formalism_L2_Th1_A_More_map_g__846035df1560
