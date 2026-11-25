-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_idx_949d3e04df5f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_idx_949d3e04df5f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:18.568698+00:00
-- url     : https://prove2.me/theorems/d9039175-09bd-501c-b4b2-09cfb5203ff8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows on Set idx 949d3e04df5f: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows on Set idx 949d3e04df5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows on Set idx 949d3e04df5f construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows on Set idx 949d3e04df5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L21-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZRowsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZRows
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZRows
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {n : ℕ} {U : Finset (Fin n)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_idx_949d3e04df5f {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (I : Cech.Idx U i) :
    onSet s I.1.1 = s I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZRows».«onSet_idx» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_idx_949d3e04df5f
