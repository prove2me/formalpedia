-- Prove2me | Theorems.Thm_VeinottBaseStock_closed_chain_has_least
-- name    : VeinottBaseStock.closed_chain_has_least
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:38:39.453712+00:00
-- url     : https://prove2.me/theorems/4d5e594e-76bb-4376-8e77-cd9f818144d3
-- title:
--   §3, p. 212 — a closed, linearly ordered, bounded-below subset of $\mathbb{R}^n$ has a minimal element
-- statement:
--   Order $\mathbb{R}^n$ componentwise. A set $A \subseteq \mathbb{R}^n$ is *linearly ordered* by $\le$ if any two of its elements $y, y'$ satisfy $y \le y'$ or $y' \le y$, and $y^* \in A$ is a *minimal element* of $A$ if $y^* \le y$ for every $y \in A$.
--
--   Let $A \subseteq \mathbb{R}^n$ be nonempty, closed, linearly ordered by $\le$ and bounded below. Then
--   $$\exists\, y^* \in A \ \text{ such that } \ y^* \le y \ \text{ for all } y \in A.$$
--
--   This is the order-theoretic fact behind the definition of $w_i(x)$, the minimal feasible inventory level used by the base stock policy.
--
--   **Formalization Note.** The paper's "minimal element" is a least element (`IsLeast`), not Mathlib's `Minimal`. The paper omits nonemptiness; the statement is false for the empty set, so `A.Nonempty` is added.
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), p. 212, §3 (sentence before the definition of w_i(x))

import Mathlib

namespace VeinottBaseStock

/-- §3, p. 212: every nonempty closed subset of `ℝⁿ` that is linearly ordered by the
componentwise order and bounded below has a least ("minimal") element. -/
theorem closed_chain_has_least {n : ℕ} (A : Set (Fin n → ℝ)) (hA : IsClosed A)
    (hchain : IsChain (· ≤ ·) A) (hne : A.Nonempty) (hbdd : BddBelow A) :
    ∃ a, IsLeast A a := by sorry

end VeinottBaseStock
