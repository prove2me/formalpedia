-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_conv_mem_dualLat
-- name    : ReciprocityTheory.PGsh.L2.conv_mem_dualLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:19.735085+00:00
-- url     : https://prove2.me/theorems/ae9f5b9d-feb1-4b13-b9a8-891ab058a7fb
-- title:
--   L2: conv mem dual Lat
-- statement:
--   The L2 construction uses the conv mem dual Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L52-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L52-L74

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
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

theorem ReciprocityTheory.PGsh.L2.conv_mem_dualLat (AA : HopfOrder (C := C) R N) {u w : N → C}
    (hu : u ∈ dualLat AA.carrier) (hw : w ∈ dualLat AA.carrier) :
    conv u w ∈ dualLat AA.carrier := by sorry
