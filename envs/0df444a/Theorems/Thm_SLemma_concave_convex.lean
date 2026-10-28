-- Prove2me | Theorems.Thm_SLemma_concave_convex
-- name    : SLemma.concave_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:00.428029+00:00
-- url     : https://prove2.me/theorems/51f6aa11-370b-4699-bf43-a2f708b0a1f8
-- title:
--   A nonnegative multiplier certifying that a concave function dominates a convex one
-- statement:
--   Let $E$ be a real vector space, let $L : E \to \mathbb{R}$ be concave and $h : E \to \mathbb{R}$
--   convex, both on all of $E$. Assume the Slater condition $L(x_0) > 0$ for some $x_0 \in E$, and
--   assume
--
--   $$
--   L(x) \ge 0 \implies h(x) \ge 0 \qquad \text{for every } x \in E .
--   $$
--
--   Then the implication is certified by a single nonnegative multiplier:
--
--   $$
--   \exists\, \tau \ge 0 \ \text{ such that } \ h(x) - \tau\, L(x) \ge 0 \quad
--   \text{for all } x \in E .
--   $$
--
--   This is the S-procedure without any quadratic structure: concavity of the constraint and
--   convexity of the objective are all the argument needs, and the ambient space need not even be
--   normed. Stated this way it covers the cases a quadratic S-lemma cannot reach -- a concave
--   constraint built from a trace or a support function, say -- and it is the form to import when
--   the two functions in hand are convex by construction rather than by a matrix.
-- source:
--   I. Polik and T. Terlaky, A survey of the S-lemma, SIAM Review 49 (2007), 371-418. Carved from https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1, lines 3808-3849 (the goal proof of DRJointCC.Joint.theorem_3_6, which re-derives it inline; the same block appears in https://prove2.me/submissions/351d29f4-df20-4118-a8bc-25a1b62a5233 for DRJointCC.Individual.theorem_2_2)

import Mathlib

open MeasureTheory Matrix
open scoped ENNReal

theorem SLemma.concave_convex {E : Type*} [AddCommGroup E] [Module ℝ E] (L h : E → ℝ)
    (hL : ConcaveOn ℝ Set.univ L) (hh : ConvexOn ℝ Set.univ h) (hslater : ∃ x₀, 0 < L x₀)
    (H : ∀ x, 0 ≤ L x → 0 ≤ h x) : ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ h x - τ * L x := by sorry
