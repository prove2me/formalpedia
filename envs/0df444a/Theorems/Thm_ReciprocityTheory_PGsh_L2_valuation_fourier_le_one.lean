-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_fourier_le_one
-- name    : ReciprocityTheory.PGsh.L2.valuation_fourier_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:06:08.12036+00:00
-- url     : https://prove2.me/theorems/badab6b4-53b0-402c-af8c-59e7bb511ecb
-- title:
--   L2: valuation fourier le one
-- statement:
--   The L2 construction uses the valuation fourier le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L135-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationFourierLeOne.lean#L135-L152

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

theorem ReciprocityTheory.PGsh.L2.valuation_fourier_le_one (v : Valuation C NNReal) (hv : v.Integers R) {H : Type}
    (χ : H → AddChar N C) (AA : HopfOrder (C := C) R N) {u : N → C}
    (hu : u ∈ dualLat AA.carrier) (h : H) :
    v (fourier (R := R) (fun h a => χ h a) u h) ≤ 1 := by sorry
