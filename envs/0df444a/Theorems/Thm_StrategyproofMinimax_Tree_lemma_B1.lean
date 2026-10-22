-- Prove2me | Theorems.Thm_StrategyproofMinimax_Tree_lemma_B1
-- name    : StrategyproofMinimax.Tree.lemma_B1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T22:18:06.420991+00:00
-- url     : https://prove2.me/theorems/5d3a785a-a417-4eb1-978d-028fa73020a5
-- title:
--   Lemma B.1 — a left leaf lᵏ with 𝔼[d(f(xᵏ), lᵏ)] ≥ (2ᵏ⁺¹ − 1)/2 − (2ᵏ⁺¹ − (k + 2))/m
-- statement:
--   Let $m\ge2$, let $2m^k$ divide $n$, and let $f:G^n\to\Delta(G)$ be a strategyproof randomized mechanism on the tree $G=G(m,k)$ such that $\mathbb E[d(f(x^0),l^0)]\ge 1/2$. Then there is a left vertex $l^k$ on level $k$ such that, for the profile $x^k$ built along the path $l^0,l^1,\dots,l^{k-1}$ to its parent,
--   $$\mathbb E\big[d(f(x^k),l^k)\big]\ \ge\ \frac{2^{k+1}-1}{2}-\frac{2^{k+1}-(k+2)}{m}.\tag{B1}$$
--   This is the paper's Lemma B.1, the core of the proof of Theorem 4.1. For $k=0$ it is the hypothesis itself (then $x^0=x^k$, $l^k=l^0$ and the bound is $1/2$).
--
--   **Formalization Note.** The vertex $l^k$ is a word $u$ of length $k$, and $x^k$ is `profileAlong m k n u.dropLast`. The hypothesis $\mathbb E[d(f(x^0),l^0)]\ge1/2$ is the paper's "without loss of generality" on p. 524 (one of $l^0$, $r^0$ satisfies it, since $d(l^0,r^0)=1$). All arithmetic is in $\mathbb R$.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 525, Lemma B.1, Eq. (B1)

import Mathlib
import Definitions.Def_StrategyproofMinimax_Tree_cost
import Definitions.Def_StrategyproofMinimax_Tree_HardTree
import Definitions.Def_StrategyproofMinimax_Tree_profileAlong

namespace StrategyproofMinimax.Tree

/-- Lemma B.1 (p. 525): for an SP mechanism `f` on `G(m, k)` with `𝔼[d(f(x⁰), l⁰)] ≥ 1/2`, there
is a left vertex `lᵏ` on level `k` (the word `u`) such that, for the profile `xᵏ` built along the
path to its parent `lᵏ⁻¹` (the word `u.dropLast`),
`𝔼[d(f(xᵏ), lᵏ)] ≥ (2ᵏ⁺¹ − 1)/2 − (2ᵏ⁺¹ − (k + 2))/m`. -/
theorem lemma_B1 {m k n : ℕ} (hm : 2 ≤ m) (hdiv : 2 * m ^ k ∣ n)
    (f : (Fin n → HardTree m k) → MeasureTheory.ProbabilityMeasure (HardTree m k))
    (hf : IsStrategyproof f)
    (h0 : (1 : ℝ) / 2 ≤ cost (f (profileZero m k n)) (vertex .left [])) :
    ∃ u : List (Fin m), u.length = k ∧
      ((2 : ℝ) ^ (k + 1) - 1) / 2 - ((2 : ℝ) ^ (k + 1) - ((k : ℝ) + 2)) / (m : ℝ) ≤
        cost (f (profileAlong m k n u.dropLast)) (vertex .left u) := by sorry

end StrategyproofMinimax.Tree
