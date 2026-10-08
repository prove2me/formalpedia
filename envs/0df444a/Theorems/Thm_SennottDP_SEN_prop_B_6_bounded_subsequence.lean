-- Prove2me | Theorems.Thm_SennottDP_SEN_prop_B_6_bounded_subsequence
-- name    : SennottDP.SEN.prop_B_6_bounded_subsequence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T09:45:42.277249+00:00
-- url     : https://prove2.me/theorems/36076d27-9f63-47ca-9375-2e336be25df7
-- title:
--   Proposition B.6 — a sequence of functions squeezed between −L and M has a pointwise convergent subsequence
-- statement:
--   Let $S$ be countable and let $L$ and $M$ be nonnegative finite functions on $S$. Let $(u_r)_{r \ge 0}$ be a sequence of real functions on $S$ with $-L \le u_r \le M$ for all $r$. Then there exist a subsequence $r_k$ and a function $w$ on $S$ with $-L \le w \le M$ such that
--
--   $$\lim_{k\to\infty} u_{r_k}(i) = w(i) \qquad \text{for all } i \in S.$$
--
--   This compactness statement is what produces limit functions of the relative value functions $h_{\alpha_n}$ in the average cost theory.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 290, Proposition B.6

import Mathlib

open Filter Topology

namespace SennottDP.SEN

/-- Sennott (1999), Proposition B.6, p. 290: let `L(i)` and `M(i)` be nonnegative (finite)
functions on the countable set `S`. Assume `u_r(i)` is a sequence of functions on `S` with
`−L ≤ u_r ≤ M` for all `r`. Then there exist a subsequence `r_k` and a function `w`, with
`−L ≤ w ≤ M`, satisfying `lim_{k→∞} u_{r_k}(i) = w(i)` for all `i ∈ S`. -/
theorem prop_B_6_bounded_subsequence {S : Type} [Countable S] (L M : S → ℝ)
    (hL : ∀ i, 0 ≤ L i) (hM : ∀ i, 0 ≤ M i) (u : ℕ → S → ℝ)
    (hu : ∀ r i, -L i ≤ u r i ∧ u r i ≤ M i) :
    ∃ rk : ℕ → ℕ, StrictMono rk ∧ ∃ w : S → ℝ, (∀ i, -L i ≤ w i ∧ w i ≤ M i) ∧
      ∀ i, Tendsto (fun k => u (rk k) i) atTop (𝓝 (w i)) := by sorry

end SennottDP.SEN
