-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_isLat_map_equiv
-- name    : ReciprocityTheory.PGsh.Up.PullbackHopfOrder.isLat_map_equiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:32.550254+00:00
-- url     : https://prove2.me/theorems/9e43436f-3a3e-4b6e-9675-6112f72fb7d3
-- title:
--   Pullback Hopf Order: is Lat map equiv
-- statement:
--   The Pullback Hopf Order construction uses the is Lat map equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsMatOfEquiv.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsMatOfEquiv.lean#L43-L53

import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsMatOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem ReciprocityTheory.PGsh.Up.PullbackHopfOrder.isLat_map_equiv {X K : Type} [Fintype X] [DecidableEq X] {_ : Fintype K} {_ : DecidableEq K}
    (e : X ≃ K) {M : Submodule R (K → C)} (hM : IsLat R M) :
    IsLat R (M.map (LinearMap.funLeft R C e)) := by sorry
