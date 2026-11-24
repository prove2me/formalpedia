-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_exists_split
-- name    : ReciprocityTheory.PGsh.Up.PullbackHopfOrder.exists_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:47.240545+00:00
-- url     : https://prove2.me/theorems/8573dd18-aec9-47cd-9cb4-b75fa963f8bd
-- title:
--   Pullback Hopf Order: exists split
-- statement:
--   The Pullback Hopf Order construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsMatOfEquiv.lean#L78-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsMatOfEquiv.lean#L78-L116

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
variable {S : Type} [CommRing S] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

theorem ReciprocityTheory.PGsh.Up.PullbackHopfOrder.exists_split (e : Matrix n n S) (he : e * e = e) (B : Matrix n k S)
    (hr : LinearMap.range B.mulVecLin = LinearMap.range e.mulVecLin)
    (hk : LinearMap.ker B.mulVecLin = ⊥) : ∃ L : Matrix k n S, L * B = 1 ∧ B * L = e := by sorry
