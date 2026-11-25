-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_cpow_mem
-- name    : ReciprocityTheory.PGsh.L2.cpow_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:26.59808+00:00
-- url     : https://prove2.me/theorems/adaf7c4e-ce96-45a7-8dc3-df25eda882b8
-- title:
--   L2: cpow mem
-- statement:
--   The L2 construction uses the cpow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L89-L92

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

theorem ReciprocityTheory.PGsh.L2.cpow_mem (AA : HopfOrder (C := C) R N) {u : N → C} (hu : u ∈ dualLat AA.carrier) :
    ∀ k, cpow u k ∈ dualLat AA.carrier
  := by sorry
