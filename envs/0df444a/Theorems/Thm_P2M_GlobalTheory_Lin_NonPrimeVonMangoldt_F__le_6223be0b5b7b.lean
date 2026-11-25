-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__le_6223be0b5b7b
-- name    : P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__le_6223be0b5b7b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:49.883566+00:00
-- url     : https://prove2.me/theorems/e48d77ea-debe-42f1-973b-eb64d40f67f0
-- title:
--   P2 M Global Theory Lin Non Prime Von Mangoldt F  le 6223be0b5b7b: P2 M Global Theory Lin Non Prime Von Mangoldt F  le 6223be0b5b7b
-- statement:
--   The P2 M Global Theory Lin Non Prime Von Mangoldt F  le 6223be0b5b7b construction uses the P2 M Global Theory Lin Non Prime Von Mangoldt F  le 6223be0b5b7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNonPrimeVonMangoldtDivRpow.lean#L20-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNonPrimeVonMangoldtDivRpow.lean#L20-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.NonPrimeVonMangoldt

theorem P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__le_6223be0b5b7b (p : Nat.Primes) (k : ℕ) :
    F₂ (p, k) ≤ 4 * (((p : ℕ) : ℝ) ^ (-(5 / 4) : ℝ) * ((2 : ℝ) ^ (-(3 / 4) : ℝ)) ^ k) := by sorry

alias «GlobalTheory».«Lin».«NonPrimeVonMangoldt».«F₂_le» := P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__le_6223be0b5b7b
