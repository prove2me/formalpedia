-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__eq_3cd59a318829
-- name    : P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__eq_3cd59a318829
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:02.543825+00:00
-- url     : https://prove2.me/theorems/338d9638-edfe-4579-ade2-f3668351ed2f
-- title:
--   P2 M Global Theory Lin Non Prime Von Mangoldt F  eq 3cd59a318829: P2 M Global Theory Lin Non Prime Von Mangoldt F  eq 3cd59a318829
-- statement:
--   The P2 M Global Theory Lin Non Prime Von Mangoldt F  eq 3cd59a318829 construction uses the P2 M Global Theory Lin Non Prime Von Mangoldt F  eq 3cd59a318829 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNonPrimeVonMangoldtDivRpow.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNonPrimeVonMangoldtDivRpow.lean#L14-L18

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

theorem P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__eq_3cd59a318829 (p : Nat.Primes) (k : ℕ) :
    F₂ (p, k) = Real.log p / ((p : ℝ) ^ (k + 2)) ^ (3 / 4 : ℝ) := by sorry

alias «GlobalTheory».«Lin».«NonPrimeVonMangoldt».«F₂_eq» := P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__eq_3cd59a318829
