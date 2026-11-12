-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_corollary_2_5
-- name    : ReadOnceParityBP.LowerBound.corollary_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:51.710045+00:00
-- url     : https://prove2.me/theorems/9d81dc1e-b158-4216-8a21-f381c99a1478
-- title:
--   Corollary 2.5 — algebraic branching-program lower bound
-- statement:
--   There exist c>0 and n₀≥2 such that, for every even n≥n₀ and every syntactically multilinear ABP P over F₂ computing the formal polynomial f of Definition 2.3 in its 2n variables,
--
--   $$|P|\ge\frac{c n^2}{(\log n)^2}.$$
--
--   One pair of constants works for every cycle length and every program. This is the algebraic hardness statement used in the Boolean transfer.
--
--   Differences from the source:
--   - encoding: cycle positions Zₙ and two n-variable blocks → Fin n for the positions and Fin n ⊕ Fin n for the variables; reason: this retains exactly 2n distinct variables and the ordinary representative order for positive even n
--   - encoding: size Ω(n²/log² n) → a positive real constant and a natural threshold at least two, quantified before n and the program, using the natural logarithm; reason: this is exactly the asymptotic statement; changing the logarithm base rescales the constant
--   - encoding: finite variable sets and finite directed acyclic multigraphs → finite numbered vertices and edges, with edge-list walks and possibly equal terminals; reason: numbering preserves parallel edges, dead edges, and every finite graph; the empty path is retained
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Corollary 2.5, p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_AlgebraicProgram
import Definitions.Def_ReadOnceParityBP_LowerBound_CanonicalMatching

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Volk, Corollary 2.5 (p. 4): every syntactically multilinear ABP over `𝔽₂` computing the
polynomial `f` of Definition 2.3 has size `Ω(n² / log² n)` (`n` even). -/
theorem corollary_2_5 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → Even n →
      ∀ P : SMABP (Fin n ⊕ Fin n) (ZMod 2), P.poly = rsyPoly (ZMod 2) n →
        c * (n : ℝ) ^ 2 / (Real.log n) ^ 2 ≤ (P.size : ℝ) := by sorry

end ReadOnceParityBP.LowerBound
