-- Prove2me | Theorems.Thm_StrategyproofMinimax_Tree_mc_ge_B1_bound
-- name    : StrategyproofMinimax.Tree.mc_ge_B1_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T22:21:02.789474+00:00
-- url     : https://prove2.me/theorems/395ae68e-259e-477c-b766-5d60bc1cf058
-- title:
--   Appendix B, p. 526 — the expected maximum distance under xᵏ is at least the right-hand side of (B1)
-- statement:
--   Under the hypotheses of Lemma B.1 and $n\ge1$ ($m\ge2$, $2m^k\mid n$, $f$ strategyproof on $G(m,k)$, $\mathbb E[d(f(x^0),l^0)]\ge1/2$), there is a left vertex $l^k$ on level $k$ such that, for the profile $x^k$ built along the path to its parent,
--   $$\operatorname{mc}\big(f(x^k),x^k\big)\ \ge\ \frac{2^{k+1}-1}{2}-\frac{2^{k+1}-(k+2)}{m}.$$
--   This is the step of the proof of Theorem 4.1 that passes from one agent's expected distance to the expected maximum distance; it uses that at least one agent sits at $l^k$ under $x^k$.
--
--   **Formalization Note.** $l^k$ is a word $u$ of length $k$, and $x^k$ is `profileAlong m k n u.dropLast`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 526, Appendix B (first sentences after Lemma B.1's proof)

import Mathlib
import Definitions.Def_StrategyproofMinimax_Tree_cost
import Definitions.Def_StrategyproofMinimax_Tree_HardTree
import Definitions.Def_StrategyproofMinimax_Tree_profileAlong

namespace StrategyproofMinimax.Tree

/-- Appendix B, p. 526: from Lemma B.1, the expected maximum distance under `xᵏ` is at least the
right-hand side of (B1): for an SP mechanism `f` on `G(m, k)` with `𝔼[d(f(x⁰), l⁰)] ≥ 1/2`, there
is a left vertex on level `k` (the word `u`) with
`mc(f(xᵏ), xᵏ) ≥ (2ᵏ⁺¹ − 1)/2 − (2ᵏ⁺¹ − (k + 2))/m`, where `xᵏ` is built along the path to `u`'s
parent. -/
theorem mc_ge_B1_bound {m k n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (hdiv : 2 * m ^ k ∣ n)
    (f : (Fin n → HardTree m k) → MeasureTheory.ProbabilityMeasure (HardTree m k))
    (hf : IsStrategyproof f)
    (h0 : (1 : ℝ) / 2 ≤ cost (f (profileZero m k n)) (vertex .left [])) :
    ∃ u : List (Fin m), u.length = k ∧
      ((2 : ℝ) ^ (k + 1) - 1) / 2 - ((2 : ℝ) ^ (k + 1) - ((k : ℝ) + 2)) / (m : ℝ) ≤
        mc (f (profileAlong m k n u.dropLast)) (profileAlong m k n u.dropLast) := by sorry

end StrategyproofMinimax.Tree
