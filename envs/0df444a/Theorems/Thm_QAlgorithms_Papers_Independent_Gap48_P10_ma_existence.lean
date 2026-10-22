-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_ma_existence
-- name    : QAlgorithms.Papers.Independent.Gap48.P10.ma_existence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:16:54.114932+00:00
-- url     : https://prove2.me/theorems/4ea973b7-2a19-4c1e-8910-1f3f7756136d
-- title:
--   Theorem 2.3: MA existence
-- statement:
--   Let $U$ be an exact single-qubit Clifford+$T$ operator, including its absolute phase. There exists Matsumoto–Amano data consisting of an optional initial $T$, a finite list of $HT$ or $SHT$ syllables, and one terminal Clifford operator $C$, such that
--
--   $$
--   U=(T\mid\varepsilon)(HT\mid SHT)^*C.
--   $$
--   Expanding the terminal and the other Clifford factors into fixed $H,S,\omega I$ words and reversing printed order gives a chronological elementary-letter list denoting exactly $U$. Its actual number of $T$ letters equals the optional leading contribution plus the number of body syllables.
--
--   This is an exact output-word interface; it makes no runtime or matrix-denominator bound claim.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, PDF p. 2, Theorem 2.3: MA existence

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Theorem 2.3, PDF p.2: exact MA existence, including the actual chronological
H/S/T/omega expansion and its actual T-letter count. These extra representation
clauses unpack the source's circuit output; no global phase is discarded. -/
theorem ma_existence (U : Mat) (hU : CliffordT U) :
    ∃ M : NormalForm, maValue M = U ∧
      chronologicalValue (normalWord cliffordH cliffordSH M) = U ∧
      letterTCount (normalWord cliffordH cliffordSH M) = normalTCount M := by sorry

end QAlgorithms.Papers.Independent.Gap48.P10

end
