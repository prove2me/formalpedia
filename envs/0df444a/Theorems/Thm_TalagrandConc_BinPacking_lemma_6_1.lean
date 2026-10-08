-- Prove2me | Theorems.Thm_TalagrandConc_BinPacking_lemma_6_1
-- name    : TalagrandConc.BinPacking.lemma_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:55.923015+00:00
-- url     : https://prove2.me/theorems/1ef031f0-69c1-478e-9ac3-86e1a43795d6
-- title:
--   Lemma 6.1 — B_N(x₁,…,x_N) ≤ 2 Σ x_i + 1
-- statement:
--   Let $x_1,\dots,x_N \in [0,1]$ be item sizes and $B_N(x_1,\dots,x_N)$ the minimum number of unit bins into which they can be packed. Then
--   $$B_N(x_1,\dots,x_N) \le 2\sum_{i \le N} x_i + 1 .$$
--
--   This deterministic bound says that the optimal number of bins is at most twice the total size plus one. It is one of the "trivial facts about bin packing" on which Talagrand's concentration argument for $B_N$ rests.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 151, Lemma 6.1

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.BinPacking

/-- Talagrand (1995), p. 151, Lemma 6.1: `B_N(x₁, …, x_N) ≤ 2 ∑_{i ≤ N} x_i + 1`. -/
theorem lemma_6_1 {N : ℕ} (x : Fin N → unitInterval) :
    (binNumber x : ℝ) ≤ 2 * ∑ i, (x i : ℝ) + 1 := by sorry

end TalagrandConc.BinPacking
