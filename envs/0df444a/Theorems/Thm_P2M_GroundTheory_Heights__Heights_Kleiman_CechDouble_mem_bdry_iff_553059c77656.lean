-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_mem_bdry_iff_553059c77656
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_mem_bdry_iff_553059c77656
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:10.188465+00:00
-- url     : https://prove2.me/theorems/e9c23913-6988-5a46-8f0e-71083950afee
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double mem bdry iff 553059c77656: P2 M Ground Theory Heights  Heights Kleiman Cech Double mem bdry iff 553059c77656
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double mem bdry iff 553059c77656 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double mem bdry iff 553059c77656 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDouble.lean#L43-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDouble.lean#L43-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDouble
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
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble
open Cech
variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {m : ℕ} {U : Finset (Fin m)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_mem_bdry_iff_553059c77656 (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) :
    ∀ (n : ℕ) (z : Cdeg (fun _ : Cell U => E) G n),
      z ∈ Stair.bdry (dRes G hG) n ↔ (z : Cochain (fun _ : Cell U => E) n) ∈
        Cech.bdryDeg (fun _ : Cell U => E) G (Cech.idRes S E U) n
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«mem_bdry_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_mem_bdry_iff_553059c77656
