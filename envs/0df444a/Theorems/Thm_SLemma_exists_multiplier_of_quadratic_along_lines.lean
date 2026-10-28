-- Prove2me | Theorems.Thm_SLemma_exists_multiplier_of_quadratic_along_lines
-- name    : SLemma.exists_multiplier_of_quadratic_along_lines
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:01.130229+00:00
-- url     : https://prove2.me/theorems/664e5986-ed50-49c4-a052-56738f0225fa
-- title:
--   A nonnegative multiplier for one function dominated by another along every line
-- statement:
--   Let $V$ be a real vector space and let $a, b : V \to \mathbb{R}$ be two functions that are
--   quadratic along every line: for all $x, y \in V$ there is a constant $k$ (depending on $x$ and
--   $y$) with
--
--   $$
--   a(x + s y) = a(x) + s\,k + s^{2} a(y) \qquad \text{for every } s \in \mathbb{R},
--   $$
--
--   and likewise for $b$ with its own constant. Assume
--
--   1. a Slater point: $b(x_0) > 0$ for some $x_0 \in V$;
--   2. implication: $b(x) \ge 0$ implies $a(x) \ge 0$, for every $x \in V$.
--
--   Then the implication is certified by a single nonnegative multiplier:
--
--   $$
--   \exists\, \tau \ge 0 \ \text{ such that } \ a(x) - \tau\, b(x) \ge 0 \quad \text{for all } x \in V .
--   $$
--
--   This is the engine of the S-lemma, stated for the weakest structure the argument needs: not
--   quadratic forms on $\mathbb{R}^n$, but any pair of functions whose restriction to a line is a
--   quadratic in the parameter. Every concrete S-procedure -- the homogeneous and inhomogeneous
--   quadratic cases, and the version for a concave function dominating a convex one -- is this
--   statement applied to a particular pair, so a formalization that wants one of them can import
--   this instead of repeating the two-roots argument.
-- source:
--   I. Polik and T. Terlaky, A survey of the S-lemma, SIAM Review 49 (2007), 371-418. Carved from https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1, lines 1085-1117 (the goal proof of DRJointCC.Joint.theorem_3_6, which re-derives it inline; the same block appears in https://prove2.me/submissions/351d29f4-df20-4118-a8bc-25a1b62a5233 for DRJointCC.Individual.theorem_2_2)

import Mathlib

open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem SLemma.exists_multiplier_of_quadratic_along_lines {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : V → ℝ)
    (ha : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, a (x + s • y) = a x + s * k + s ^ 2 * a y)
    (hb : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, b (x + s • y) = b x + s * k + s ^ 2 * b y)
    (hslater : ∃ x₀, 0 < b x₀) (H : ∀ x, 0 ≤ b x → 0 ≤ a x) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ a x - τ * b x := by sorry
