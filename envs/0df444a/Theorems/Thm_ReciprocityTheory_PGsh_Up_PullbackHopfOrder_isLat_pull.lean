-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_isLat_pull
-- name    : ReciprocityTheory.PGsh.Up.PullbackHopfOrder.isLat_pull
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:21.980013+00:00
-- url     : https://prove2.me/theorems/155ad529-8e43-432b-ab93-febfd5203f6d
-- title:
--   Pullback Hopf Order: is Lat pull
-- statement:
--   The Pullback Hopf Order construction uses the is Lat pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsMatOfEquiv.lean#L58-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsMatOfEquiv.lean#L58-L70

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

theorem ReciprocityTheory.PGsh.Up.PullbackHopfOrder.isLat_pull (v : Valuation C NNReal) (hv : v.Integers R) {N X : Type} [AddCommGroup N]
    [Fintype N] [DecidableEq N] [AddCommGroup X] [Fintype X] [DecidableEq X]
    (ψ : X →+ N) (hψ : Function.Injective ψ) (AA : HopfOrder (C := C) R N) :
    IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ)) := by sorry
