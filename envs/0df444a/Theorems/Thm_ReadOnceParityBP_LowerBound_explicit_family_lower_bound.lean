-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_explicit_family_lower_bound
-- name    : ReadOnceParityBP.LowerBound.explicit_family_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:29:05.064018+00:00
-- url     : https://prove2.me/theorems/ccd297ab-6385-482f-bfed-f46c7e99595f
-- title:
--   Theorem 1.2 — explicit almost quadratic parity-program lower bound
-- statement:
--   There is a single Boolean family F_N:{0,1}^N→{0,1}, defined at every natural input length N, that is computed by one deterministic polynomial-time Turing machine. There are also c>0 and N₀≥2 such that for every N≥N₀ and every read-once parity branching program P computing F_N,
--
--   $$|P|\ge\frac{c N^2}{(\log N)^2}.$$
--
--   The size is the number of edges of the finite acyclic multigraph. The bound includes unlayered programs, arbitrary degrees, parallel edges, and syntactic read-once paths even when they are inconsistent. F, its uniform machine, c, and N₀ are conclusions of the theorem and are independent of the varying input length and program. This combines full hardness with uniform explicitness at all lengths.
--
--   Differences from the source:
--   - encoding: finite variable sets and finite directed acyclic multigraphs → finite numbered vertices and edges, with edge-list walks and possibly equal terminals; reason: numbering preserves parallel edges, dead edges, and every finite graph; the empty path is retained
--   - encoding: size Ω(n²/log² n) → a positive real constant and a natural threshold at least two, quantified before n and the program, using the natural logarithm; reason: this is exactly the asymptotic statement; changing the logarithm base rescales the constant
--   - encoding: a polynomial-time Turing machine on raw input bits → Nonempty of Mathlib TM2ComputableInPolyTime for one list function, agreeing with all family members; reason: the certificate contains one finite machine and one polynomial bound on its actual steps, including one-bit output
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Theorem 1.2 and following explicitness sentence, p.2; model discussion p.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_ParityProgram
import Definitions.Def_ReadOnceParityBP_LowerBound_Explicit

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Theorem 1.2 (p. 2): there is an explicit family `{f_N : {0,1}^N → {0,1}}_{N ∈ ℕ}`
(computed by one polynomial-time Turing machine) such that every read-once parity branching
program computing `f_N` has size `Ω(N² / log² N)`. -/
theorem explicit_family_lower_bound :
    ∃ F : (N : ℕ) → (Fin N → Bool) → Bool, Explicit F ∧
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        ∀ P : ParityBP (Fin N), P.Computes (F N) →
          c * (N : ℝ) ^ 2 / (Real.log N) ^ 2 ≤ (P.size : ℝ) := by sorry

end ReadOnceParityBP.LowerBound
