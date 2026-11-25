-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_hdeg_equiv_bba7c94c79f8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_hdeg_equiv_bba7c94c79f8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:35.837527+00:00
-- url     : https://prove2.me/theorems/e1a14dec-4fca-43de-bda0-0a21adf8d26e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double hdeg equiv bba7c94c79f8: P2 M Ground Theory Heights  Heights Kleiman Cech Double hdeg equiv bba7c94c79f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double hdeg equiv bba7c94c79f8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double hdeg equiv bba7c94c79f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDouble.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDouble.lean#L61-L73

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_hdeg_equiv_bba7c94c79f8 (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (n : ℕ) :
    Nonempty (Cech.Hdeg (fun _ : Cell U => E) G (Cech.idRes S E U) n ≃ₗ[S] Stair.H (dRes G hG) n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«hdeg_equiv» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_hdeg_equiv_bba7c94c79f8
