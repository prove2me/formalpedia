-- Prove2me | Theorems.Thm_SubmodOrder_large_singleton_case
-- name    : SubmodOrder.large_singleton_case
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:38:48.898394+00:00
-- url     : https://prove2.me/theorems/5a4c645b-fae8-4406-b8fa-9b3c707f12f6
-- title:
--   Proof of Theorem 2, p.21 — if $\mathrm{OPT}\le2\max_e f(\{e\})$ then $f(S_L)\ge(1-\varepsilon)\tfrac12\mathrm{OPT}$ (corrected: $k=1$)
-- statement:
--   Let $f$ be monotone with $f(\emptyset)=0$, let $k\ge1$ and $\varepsilon\in(0,1)$, and let
--
--   $$
--   \tau=\frac1k\max_{e\in N}f(\{e\}),\qquad L=\max\bigl(1,\lceil\log_{1+\varepsilon}k\rceil\bigr).
--   $$
--
--   If $\mathrm{OPT}\le2\max_{e\in N}f(\{e\})$, then the last set of Algorithm 1, the output $S_L$ of Threshold Add$(k,(1+\varepsilon)^{L-1}\tau)$, satisfies
--
--   $$
--   f(S_L)\ \ge\ (1-\varepsilon)\cdot\tfrac12\cdot\mathrm{OPT}.
--   $$
--
--   The threshold $(1+\varepsilon)^{L-1}\tau$ lies between $\max_e f(\{e\})/(1+\varepsilon)$ and $\max_e f(\{e\})$. This disposes of the case in which a single element is worth at least half the optimum.
--
--   Differences from the source:
--   - correction: the set S_{⌈log_{1+ε} k⌉} → S_L with L = numRounds k ε = max(1, ⌈log_{1+ε} k⌉); reason: at k = 1 the printed index is 0 and names no set of Algorithm 1 (whose loop is empty there); for k ≥ 2 the index is the printed one
--   - generalization: f monotone and subadditive with a weak submodular order → f monotone with f(∅) = 0, no subadditivity and no order hypothesis; reason: the case uses only f(S) ≥ |S|τ for Threshold Add and the value of the best singleton; it specializes to the paper's f
--   - encoding: max_{e∈N} f({e}) → maxSingleton f = max(0, max_e f({e})); reason: equal for monotone f with f(∅) = 0 on a nonempty ground set; on the empty ground set it is 0, where OPT = 0
--   - encoding: OPT, the optimal value of max f(S) over |S| ≤ k → StreamSubmod.optVal f k (published definition, reused), a finite maximum over the subsets of the Fintype α with at most k elements; reason: same value; ∅ is feasible, so the family is nonempty
--   - encoding: S_L, the L-th set computed by Algorithm 1 → the output of thresholdAdd π k ((1 + ε)^(L−1) · maxSingleton f / k); reason: Algorithm 1 computes the same threshold from its singleton queries
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, proof of Theorem 2, p.21

import Mathlib
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_SubmodOrder_maxSingleton
import Definitions.Def_SubmodOrder_OracleProg
import Definitions.Def_SubmodOrder_thresholdAdd
import Definitions.Def_SubmodOrder_algorithm1

namespace SubmodOrder

/-- The large-singleton case (Udwani, arXiv:2107.02743v5, proof of Theorem 2, p.21: "Notice that
for OPT ≤ 2maxe∈N f({e}), we have f(S⌈log1+ε k⌉) ≥ (1 − ε)0.5OPT.").

Let `f` be monotone with `f(∅) = 0`, `k ≥ 1`, `ε ∈ (0,1)`, `τ = 1/k max_e f({e})` and
`L = max(1, ⌈log_{1+ε} k⌉)`. If `OPT ≤ 2 max_e f({e})`, then the output `S_L` of
Threshold Add(k, (1 + ε)^{L−1} τ), the last set of Algorithm 1, satisfies
`f(S_L) ≥ (1 − ε) · ½ · OPT`.

**Formalization Note.** `max_e f({e})` is `maxSingleton f = max(0, max_e f({e}))`, equal to the
paper's maximum for monotone `f` with `f ∅ = 0` on a nonempty ground set. The index
`L = numRounds k ε` is the printed `⌈log_{1+ε} k⌉` for `k ≥ 2` and `1` for `k = 1`, where the
printed index `0` names no set of the algorithm. -/
theorem large_singleton_case {α : Type} [Fintype α] [DecidableEq α] {n : ℕ} (π : α ≃ Fin n)
    (f : Finset α → ℝ) (hmono : Monotone f) (hf0 : f ∅ = 0) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hopt : StreamSubmod.optVal f k ≤ 2 * maxSingleton f) :
    (1 - ε) * (1 / 2) * StreamSubmod.optVal f k ≤
      f (OracleProg.run f
        (thresholdAdd π k ((1 + ε) ^ (numRounds k ε - 1) * (maxSingleton f / k)))).1 := by sorry

end SubmodOrder
