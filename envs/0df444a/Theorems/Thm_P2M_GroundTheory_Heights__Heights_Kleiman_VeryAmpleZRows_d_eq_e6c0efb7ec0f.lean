-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_d_eq_e6c0efb7ec0f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_d_eq_e6c0efb7ec0f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:02:21.635803+00:00
-- url     : https://prove2.me/theorems/cf122b6c-a4ff-5a35-a48e-3bff34237342
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows d eq e6c0efb7ec0f: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows d eq e6c0efb7ec0f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows d eq e6c0efb7ec0f construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZRows d eq e6c0efb7ec0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZRows.lean#L26-L32

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_d_eq_e6c0efb7ec0f {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (K : Cech.Idx U (i + 1)) :
    Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZRows».«d_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_d_eq_e6c0efb7ec0f
