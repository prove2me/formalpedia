-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_dualLat_map_fourier
-- name    : ReciprocityTheory.PGsh.L2.mem_dualLat_map_fourier
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:24.262809+00:00
-- url     : https://prove2.me/theorems/c96b28c1-0120-59ce-825f-9b68369429a1
-- title:
--   L2: mem dual Lat map fourier
-- statement:
--   The L2 construction uses the mem dual Lat map fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L180-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L180-L191

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem ReciprocityTheory.PGsh.L2.mem_dualLat_map_fourier (e : H ≃ AddChar N C) (M : Submodule R (N → C)) (w : H → C) :
    w ∈ dualLat (M.map (fourier (R := R) fun h a => e h a)) ↔
      fourier (R := R) (fun a h => e h a) w ∈ dualLat M := by sorry
