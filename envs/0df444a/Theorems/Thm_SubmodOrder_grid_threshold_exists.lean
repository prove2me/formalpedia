-- Prove2me | Theorems.Thm_SubmodOrder_grid_threshold_exists
-- name    : SubmodOrder.grid_threshold_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:08.455069+00:00
-- url     : https://prove2.me/theorems/6536c8d6-24d3-42f8-85f2-d5c6cdbb6ed6
-- title:
--   Proof of Theorem 2, p.21 — if $\mathrm{OPT}>2\max_e f(\{e\})$, some grid threshold $\tau_i$ lies in $[(1-\varepsilon)\mathrm{OPT}/(2k),\,\mathrm{OPT}/(2k)]$
-- statement:
--   Let $f$ be monotone and subadditive with $f(\emptyset)=0$, let $k\ge1$ and $\varepsilon\in(0,1)$, and let
--
--   $$
--   \tau=\frac1k\max_{e\in N}f(\{e\}),\qquad \tau_i=\tau(1+\varepsilon)^{i-1},\qquad L=\max\bigl(1,\lceil\log_{1+\varepsilon}k\rceil\bigr).
--   $$
--
--   If $\mathrm{OPT}>2\max_{e\in N}f(\{e\})$, then there is an $i\in\{1,\dots,L\}$ with
--
--   $$
--   \frac{(1-\varepsilon)\,\mathrm{OPT}}{2k}\ \le\ \tau_i\ \le\ \frac{\mathrm{OPT}}{2k}.
--   $$
--
--   Together with the single-threshold guarantee this shows that one of the sets $S_1,\dots,S_L$ of Algorithm 1 is a $(1-\varepsilon)\frac12$-approximation.
--
--   Differences from the source:
--   - generalization: π a weak submodular order of f → no order hypothesis; reason: the step uses only OPT ≤ k · max_e f({e}), which follows from subadditivity and f(∅) = 0; it specializes to the paper's f
--   - encoding: i ∈ {1, …, ⌈log_{1+ε} k⌉} → 1 ≤ i ≤ numRounds k ε = max(1, ⌈log_{1+ε} k⌉); reason: equal for k ≥ 2; at k = 1 the hypothesis OPT > 2 max_e f({e}) cannot hold, since OPT ≤ max_e f({e}) by subadditivity, so no instance changes
--   - encoding: max_{e∈N} f({e}) → maxSingleton f = max(0, max_e f({e})); reason: equal for monotone f with f(∅) = 0 on a nonempty ground set; on the empty ground set it is 0, where OPT = 0
--   - encoding: OPT, the optimal value of max f(S) over |S| ≤ k → StreamSubmod.optVal f k (published definition, reused), a finite maximum over the subsets of the Fintype α with at most k elements; reason: same value; ∅ is feasible, so the family is nonempty
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, proof of Theorem 2, p.21

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_SubmodOrder_maxSingleton
import Definitions.Def_SubmodOrder_algorithm1

namespace SubmodOrder

/-- A grid threshold lands in the window (Udwani, arXiv:2107.02743v5, proof of Theorem 2, p.21:
"So from here on we let OPT > 2maxe∈N f({e}). Consequently, there exists an i such that
(1 − ε)OPT/(2k) ≤ τi ≤ OPT/(2k).").

Let `f` be monotone and subadditive with `f(∅) = 0`, `k ≥ 1` and `ε ∈ (0,1)`; let
`τ = 1/k max_e f({e})`, `τ_i = τ(1 + ε)^{i−1}` and `L = max(1, ⌈log_{1+ε} k⌉)`. If
`OPT > 2 max_e f({e})`, then some `i ∈ {1, …, L}` has `(1 − ε) OPT/(2k) ≤ τ_i ≤ OPT/(2k)`.

**Formalization Note.** `max_e f({e})` is `maxSingleton f = max(0, max_e f({e}))`;
`L = numRounds k ε` is the printed `⌈log_{1+ε} k⌉` for `k ≥ 2` and `1` for `k = 1`. -/
theorem grid_threshold_exists {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)
    (hmono : Monotone f) (hsub : Subadditive f) (hf0 : f ∅ = 0) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hopt : 2 * maxSingleton f < StreamSubmod.optVal f k) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ numRounds k ε ∧
      (1 - ε) * StreamSubmod.optVal f k / (2 * k) ≤ (1 + ε) ^ (i - 1) * (maxSingleton f / k) ∧
      (1 + ε) ^ (i - 1) * (maxSingleton f / k) ≤ StreamSubmod.optVal f k / (2 * k) := by sorry

end SubmodOrder
