-- Prove2me | Theorems.Thm_PrizeAlloc_Interval_theorem_1_step_2
-- name    : PrizeAlloc.Interval.theorem_1_step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:40.54818+00:00
-- url     : https://prove2.me/theorems/4d9ce089-3d16-4752-a450-eb83adbe5353
-- title:
--   Theorem 1, Step 2 (p. 29) — the two-competitor restriction is an interval rule, display (9)
-- statement:
--   Let $U$ be a countable set of at least three potential competitors and $\varphi$ a prize allocation rule satisfying order preservation, endowment monotonicity and consistency. Let $N = \{1, 2\}$ be two competitors ranked $\mathcal R(1) = 1$, $\mathcal R(2) = 2$. Then there are pairwise disjoint open intervals $(a_k, b_k)$, $k = 1, 2, \dots$, with $a_k \in \mathbb R_+$, $b_k \in \mathbb R_+ \cup \{+\infty\}$, $a_k \le b_k$, such that for every $E \ge 0$
--   $$\varphi(N, \mathcal R, E) = \begin{cases} (E - a_k,\ a_k) & \text{if } a_k + a_k \le E \le b_k + a_k; \\ (b_k,\ E - b_k) & \text{if } b_k + a_k \le E \le b_k + b_k; \\ (E/2,\ E/2) & \text{otherwise.} \end{cases}$$
--
--   This is display (9) of the proof of Theorem 1, the two-competitor case of the interval-rule formula; Lemmas 2 and 3 then extend it to all competitions.
--
--   **Formalization Note** The two competitors are distinct elements $u, v$ of $U$, the ranking is the list $[u, v]$, and the intervals may depend on $(u, v)$ (the page passes to all pairs by anonymity afterwards). Endpoints $b_k$ are extended reals; with $b_k = +\infty$ the second case cannot fire. The cases are implications, and "otherwise" is $E \notin [2a_k, 2b_k]$ for every $k$; "$E/2$" on the page is the allocation $(E/2, E/2)$.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 29, proof of Theorem 1, Step 2, display (9)

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.Interval

theorem theorem_1_step_2 {U : Type*} [DecidableEq U] [Countable U]
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (hOP : OrderPreserving φ) (hEM : EndowmentMonotone φ) (hCons : Consistent φ)
    (u v : U) (huv : u ≠ v) :
    ∃ (a : ℕ → ℝ) (b : ℕ → EReal),
      (∀ k, 0 ≤ a k ∧ (a k : EReal) ≤ b k) ∧
      Pairwise (fun k k' =>
        Disjoint (Set.Ioo (a k : EReal) (b k)) (Set.Ioo (a k' : EReal) (b k'))) ∧
      ∀ E : ℝ, 0 ≤ E →
        (∀ k, ((a k + a k : ℝ) : EReal) ≤ E ∧ (E : EReal) ≤ b k + (a k : EReal) →
          φ [u, v] E u = E - a k ∧ φ [u, v] E v = a k) ∧
        (∀ k, b k + (a k : EReal) ≤ E ∧ (E : EReal) ≤ b k + b k →
          (φ [u, v] E u : EReal) = b k ∧ (φ [u, v] E v : EReal) = (E : EReal) - b k) ∧
        ((∀ k, ¬ (((a k + a k : ℝ) : EReal) ≤ E ∧ (E : EReal) ≤ b k + b k)) →
          φ [u, v] E u = E / 2 ∧ φ [u, v] E v = E / 2) := by sorry

end PrizeAlloc.Interval
