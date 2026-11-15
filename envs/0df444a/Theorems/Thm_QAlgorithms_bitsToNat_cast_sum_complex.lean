-- Prove2me | Theorems.Thm_QAlgorithms_bitsToNat_cast_sum_complex
-- name    : QAlgorithms.bitsToNat_cast_sum_complex
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-14T21:42:20.299552+00:00
-- url     : https://prove2.me/theorems/b3639ed0-ab2f-4f4a-a7d9-19791c657d2f
-- title:
--   Complex binary-weight sum equals `bitsToNat`
-- statement:
--   For an $n$-qubit computational-basis string $z$, summing the complex weights $2^{n-1-i}$ over precisely the wires whose bit is one gives the complex cast of the represented integer `bitsToNat z`. The indexing is most-significant-bit first, matching the Fourier-transform convention.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28), Eqs. (44)–(48); binary convention from de Wolf, Quantum Computing: Lecture Notes, §4.5.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QAlgorithms

/-- The most-significant-bit wire-weight sum, cast to ℂ, equals `bitsToNat`. -/
theorem bitsToNat_cast_sum_complex {n : ℕ} (z : Qubits n) :
    (∑ i : Fin n, if z i then (2 : ℂ) ^ (n - 1 - (i : ℕ)) else 0) =
      (bitsToNat z : ℂ) := by sorry

end QAlgorithms
