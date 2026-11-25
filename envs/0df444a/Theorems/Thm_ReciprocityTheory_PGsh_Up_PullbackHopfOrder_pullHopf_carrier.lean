-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_pullHopf_carrier
-- name    : ReciprocityTheory.PGsh.Up.PullbackHopfOrder.pullHopf_carrier
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:54.614188+00:00
-- url     : https://prove2.me/theorems/0da69d95-3308-4aaf-8425-2809d06c9c89
-- title:
--   Pullback Hopf Order: pull Hopf carrier
-- statement:
--   The Pullback Hopf Order construction uses the pull Hopf carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsMatOfEquiv.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsMatOfEquiv.lean#L38-L41

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

theorem ReciprocityTheory.PGsh.Up.PullbackHopfOrder.pullHopf_carrier {N X : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    [AddCommGroup X] [Fintype X] [DecidableEq X] (ψ : X →+ N) (AA : HopfOrder (C := C) R N)
    (hlat : IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ))) :
    (pullHopf ψ AA hlat).carrier = AA.carrier.map (LinearMap.funLeft R C ψ) := by sorry
