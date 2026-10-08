-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_lemma4
-- name    : SongZipkinFluct.FixedCost.lemma4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:52.922984+00:00
-- url     : https://prove2.me/theorems/3f0870f0-aa13-411d-b6a7-18ed6903280c
-- title:
--   Lemma 4 — under (11) the value iterates of (10) satisfy 0 ≤ W_n(i, x) ≤ W^B(x) for a nondecreasing W^B
-- statement:
--   Assume the standing hypotheses of the model and Assumption 1, $\alpha\bar c < p$. Let $K \ge 0$ be a fixed order cost and $W_0$ a terminal cost such that, for some nondecreasing function $W^B_0 : \mathbb Z \to \mathbb R$,
--   $$
--   0 \le W_0(i, x) \le W^B_0(x)\quad\text{for all } i \text{ and } x. \tag{11}
--   $$
--   Then there is a nondecreasing function $W^B : \mathbb Z \to \mathbb R$ such that the iterates of the recursion (10) satisfy, for all $n \ge 1$, all $i \in I$ and all $x$,
--   $$
--   0 \le W_n(i, x) \le W^B(x). \tag{12}
--   $$
--
--   The bound is uniform in the world state and in $n$; it is what makes the series $\sum_{j\ne i} q_{ij}W_{n-1}(j, y)$ in (10) converge and the limits $W_\infty = \sup_n W_n$ finite, both for the linear model ($K = 0$, $W_0 \equiv 0$) and for the fixed-cost model ($W_0 = W_\infty$ of the linear model).
--
--   **Formalization Note** "Finite" is automatic for real-valued functions. The statement holds for every $K \ge 0$ and every $W_0$ satisfying (11).
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 356, Lemma 4

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open Filter Topology

namespace SongZipkinFluct.FixedCost

open Model

/-- Lemma 4 (p. 356) of Song and Zipkin, *Inventory Control in a Fluctuating Demand
Environment*, Oper. Res. 41(2):351–370 (1993). Under the standing hypotheses and Assumption 1
(`αc̄ < p`, p. 356), for any fixed cost `K ≥ 0` and any terminal cost `W₀` with
`0 ≤ W₀(i, x) ≤ W^B_0(x)` for all `i` (11), where `W^B_0` is nondecreasing, there is a
nondecreasing `W^B` with `0 ≤ W_n(i, x) ≤ W^B(x)` for all `n ≥ 1` and all `i` (12).

Formalization Note: "finite" is automatic for real-valued functions. The lemma is stated for
the general recursion (10) and any `K ≥ 0`; it covers both the linear model (`K = 0`,
`W₀ ≡ 0`, which makes `Wlin` honest) and the fixed-cost model (`K = K̄F̃_L(α)`,
`W₀ = Wlin`). -/
theorem lemma4 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (K : ℝ) (hK : 0 ≤ K)
    (W₀ : I → ℤ → ℝ) (WB₀ : ℤ → ℝ) (hWB₀ : Monotone WB₀)
    (h11 : ∀ i x, 0 ≤ W₀ i x ∧ W₀ i x ≤ WB₀ x) :
    ∃ WB : ℤ → ℝ, Monotone WB ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i x, 0 ≤ W M K W₀ n i x ∧ W M K W₀ n i x ≤ WB x := by sorry

end SongZipkinFluct.FixedCost
