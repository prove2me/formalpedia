-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateTransport___61af264f7b42
-- name    : P2M_GroundTheory_GroupCoh_tateTransport___61af264f7b42
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:53:43.351124+00:00
-- url     : https://prove2.me/theorems/04b904af-eaa5-4d67-9b42-4bd88bf4e2ad
-- title:
--   P2 M Ground Theory Group Coh tate Transport   61af264f7b42: P2 M Ground Theory Group Coh tate Transport   61af264f7b42
-- statement:
--   The P2 M Ground Theory Group Coh tate Transport   61af264f7b42 construction uses the P2 M Ground Theory Group Coh tate Transport   61af264f7b42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateTransport.lean#L104-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateTransport.lean#L104-L111

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology groupHomology
universe u
variable {k H K : Type u} [CommRing k] [Group H] [Group K]
variable [Fintype H] [Fintype K] (e : H ≃* K)

theorem P2M_GroundTheory_GroupCoh_tateTransport___61af264f7b42 {X : ShortComplex (Rep.{u} k K)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateTransport e (n + 1)).app X.X₁ =
      (tateTransport e n).app X.X₃ ≫
        TateCohomology.δ (shortExact_map_resFunctor_equiv e hX) n := by sorry

alias «GroundTheory».«GroupCoh».«tateTransport_δ» := P2M_GroundTheory_GroupCoh_tateTransport___61af264f7b42
