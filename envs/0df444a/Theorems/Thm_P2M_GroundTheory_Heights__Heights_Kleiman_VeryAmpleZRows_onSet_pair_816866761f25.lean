-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_pair_816866761f25
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_pair_816866761f25
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:00:28.745675+00:00
-- url     : https://prove2.me/theorems/da89c0ff-2cc1-4777-ae6b-b01bc7b1e647
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows on Set pair 816866761f25: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows on Set pair 816866761f25
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows on Set pair 816866761f25 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows on Set pair 816866761f25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L34-L49

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_pair_816866761f25 {s : Cech.Cochain (fun _ : Cell U => V) 0}
    (hs : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 s = 0) {a b : Fin n} (ha : a ∈ U) (hb : b ∈ U)
    (hab : a < b) : onSet s {a} = onSet s {b} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZRows».«onSet_pair» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_pair_816866761f25
