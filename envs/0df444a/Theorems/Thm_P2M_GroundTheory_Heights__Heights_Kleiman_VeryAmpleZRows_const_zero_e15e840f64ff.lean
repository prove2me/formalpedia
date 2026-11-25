-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_const_zero_e15e840f64ff
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_const_zero_e15e840f64ff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:00:04.520355+00:00
-- url     : https://prove2.me/theorems/db0b00ab-de48-436f-8d44-1b0421ff791a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows const zero e15e840f64ff: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows const zero e15e840f64ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows const zero e15e840f64ff construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows const zero e15e840f64ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L51-L61

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_const_zero_e15e840f64ff {s : Cech.Cochain (fun _ : Cell U => V) 0}
    (hs : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 s = 0) (I K : Cech.Idx U 0) : s I = s K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZRows».«const_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_const_zero_e15e840f64ff
