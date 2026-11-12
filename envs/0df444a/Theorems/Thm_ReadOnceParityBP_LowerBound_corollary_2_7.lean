-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_corollary_2_7
-- name    : ReadOnceParityBP.LowerBound.corollary_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:28:07.626753+00:00
-- url     : https://prove2.me/theorems/cf78dfc5-31ee-4a0d-98d0-95c6b25a31d3
-- title:
--   Corollary 2.7 — Boolean hardness of the matching construction
-- statement:
--   There exist c>0 and n₀≥2 such that, for every even n≥n₀, every read-once parity branching program P computing f_bool from Definition 2.3 on its 2n input bits satisfies
--
--   $$|P|\ge\frac{c n^2}{(\log n)^2}.$$
--
--   Programs are arbitrary finite acyclic multigraphs with the source's syntactic read-once restriction. This gives hardness of the constructed Boolean functions, before the uniform computation and all-length padding obligations are joined.
--
--   Differences from the source:
--   - encoding: cycle positions Zₙ and two n-variable blocks → Fin n for the positions and Fin n ⊕ Fin n for the variables; reason: this retains exactly 2n distinct variables and the ordinary representative order for positive even n
--   - encoding: size Ω(n²/log² n) → a positive real constant and a natural threshold at least two, quantified before n and the program, using the natural logarithm; reason: this is exactly the asymptotic statement; changing the logarithm base rescales the constant
--   - encoding: finite variable sets and finite directed acyclic multigraphs → finite numbered vertices and edges, with edge-list walks and possibly equal terminals; reason: numbering preserves parallel edges, dead edges, and every finite graph; the empty path is retained
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Corollary 2.7, p.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_ParityProgram
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Corollary 2.7 (p. 5): for `f` as in Definition 2.3, `f_bool` (a Boolean function of
the `2n` bits `x_0, …, x_{n-1}, y_0, …, y_{n-1}`) requires read-once ⊕-BPs of size
`Ω(n² / log² n)` (`n` even). -/
theorem corollary_2_7 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → Even n →
      ∀ P : ParityBP (Fin n ⊕ Fin n), P.Computes (fBool n) →
        c * (n : ℝ) ^ 2 / (Real.log n) ^ 2 ≤ (P.size : ℝ) := by sorry

end ReadOnceParityBP.LowerBound
