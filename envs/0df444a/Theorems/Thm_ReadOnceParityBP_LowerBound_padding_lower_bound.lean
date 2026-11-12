-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_padding_lower_bound
-- name    : ReadOnceParityBP.LowerBound.padding_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:29:18.510253+00:00
-- url     : https://prove2.me/theorems/f8ee7f9c-9d7c-47a6-bd69-9de6662c34ab
-- title:
--   Theorem 1.2 — lower-bound padding to every input length
-- statement:
--   Assume there are c>0 and n₀≥2 such that every syntactically read-once parity program computing the 2n-bit function f_bool has at least cn²/(log n)² edges for every even n≥n₀. Then there are c′>0 and N₀≥2 such that every N≥N₀ and every read-once parity program P computing the padded family member obey
--
--   $$|P|\ge\frac{c' N^2}{(\log N)^2}.$$
--
--   The family uses n=2⌊N/4⌋ positions and at most three dummy bits. This is the all-length reindexing obligation; the assumption is the previously stated constructed-function lower bound, not the desired all-length conclusion.
--
--   Differences from the source:
--   - encoding: size Ω(n²/log² n) → a positive real constant and a natural threshold at least two, quantified before n and the program, using the natural logarithm; reason: this is exactly the asymptotic statement; changing the logarithm base rescales the constant
--   - encoding: the explicit family on every length → padding with n=2⌊N/4⌋, with shorter than four bits assigned false; reason: n≥N/4 for N≥8 and dummy-bit restriction preserves read-once and cannot increase the number of edges
--   - encoding: finite variable sets and finite directed acyclic multigraphs → finite numbered vertices and edges, with edge-list walks and possibly equal terminals; reason: numbering preserves parallel edges, dead edges, and every finite graph; the empty path is retained
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Theorem 1.2 p.2, all-length reindexing of Definition 2.3 p.4 and Corollary 2.7 p.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_Explicit
import Definitions.Def_ReadOnceParityBP_LowerBound_ParityProgram

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Theorem 1.2's all-length bookkeeping from Corollary 2.7. Constants are
uniform, and restricting dummy inputs preserves syntactic read-once and edge size. -/
theorem padding_lower_bound
    (hbound : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ,
      n₀ ≤ n → Even n → ∀ P : ParityBP (Fin n ⊕ Fin n),
        P.Computes (fBool n) → c * (n : ℝ) ^ 2 / (Real.log n) ^ 2 ≤ (P.size : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ P : ParityBP (Fin N), P.Computes (paddedFamily N) →
        c * (N : ℝ) ^ 2 / (Real.log N) ^ 2 ≤ (P.size : ℝ) := by sorry

end ReadOnceParityBP.LowerBound
