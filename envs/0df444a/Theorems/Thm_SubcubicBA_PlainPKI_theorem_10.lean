-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_10
-- name    : SubcubicBA.PlainPKI.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:42:54.29805+00:00
-- url     : https://prove2.me/theorems/e607c96b-5269-45c6-b7d1-59c32c6676e2
-- title:
--   Theorem 10 — linear rounds
-- statement:
--   For every constant $C_0>0$ there are $B_0,c_0>0$ such that for all $B\ge B_0$ and $c\ge c_0$ there is $A>0$ with the following property. For every $\kappa\ge1$ and every function $R\ge0$ with $R(1)\le1$ satisfying, at the same parameter rule as Theorem 9, the round recurrence
--   $$R(n)\le2R(\lceil n/2\rceil)+C_0\Big(\frac nm\Big)^{1/3}\big(b+R(\lceil n/m\rceil)\big)\qquad(n\ge2),$$
--   and every $n\ge1$,
--   $$R(n)\le A\,n.$$
--
--   Applied to the round complexity of the protocol, this is $R_{BA}(n)=O(n)$, the optimal round complexity.
--
--   Differences from the source:
--   - generalization: R_BA(n), the round complexity of the protocol → any nonnegative R with R(1) ≤ 1 satisfying the displayed recurrence; reason: the recurrence holds for R_BA (pp. 34–35); the theorem specializes to it
--   - generalization: "using the same parameters as Theorem 9", i.e. in the κ-regime of Theorem 9 → every κ ≥ 1, without the bound κ ≤ K log^C n; reason: the proof uses only κ⁴ < n/B in the second case; the regime of Theorem 9 is a special case
--   - encoding: O(·) and "the same parameters for b and m" → one constant C₀; ∃ B₀, c₀ ∀ B ≥ B₀, c ≥ c₀ ∃ A; reason: the shape shared with Theorem 9, so that one (B, c) serves both
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 10, p. 35 (recurrence after line 1045)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Recurrences

namespace SubcubicBA.PlainPKI

/-- Theorem 10 (p. 35). -/
theorem theorem_10 (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ B₀ c₀ : ℝ, 0 < B₀ ∧ 0 < c₀ ∧ ∀ B c : ℝ, B₀ ≤ B → c₀ ≤ c → ∃ A : ℝ, 0 < A ∧
      ∀ (κ : ℕ) (R : ℕ → ℝ), 1 ≤ κ → RoundRecurrence C₀ B c κ R →
        ∀ n : ℕ, 1 ≤ n → R n ≤ A * n := by sorry

end SubcubicBA.PlainPKI
