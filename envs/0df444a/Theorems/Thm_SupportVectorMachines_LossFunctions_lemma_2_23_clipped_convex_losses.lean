-- Prove2me | Theorems.Thm_SupportVectorMachines_LossFunctions_lemma_2_23_clipped_convex_losses
-- name    : SupportVectorMachines.LossFunctions.lemma_2_23_clipped_convex_losses
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:38.244225+00:00
-- url     : https://prove2.me/theorems/3a52f279-e02f-45d7-aafe-724c6b0f3911
-- title:
--   Lemma 2.23 — a convex loss can be clipped at $M$ iff it has a minimizer in $[-M,M]$
-- statement:
--   This is Lemma 2.23 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 34): an elementary criterion for when a convex loss can be clipped.
--
--   Let $L : X \times Y \times \mathbb R \to [0,\infty)$ be a loss function such that
--   $L(x,y,\cdot) : \mathbb R \to [0,\infty)$ is convex for every $x \in X$, $y \in Y$, and let
--   $M > 0$. Then the following are equivalent:
--
--   1. $L$ can be clipped at $M$ (Definition 2.22): $L(x,y,\widehat t) \le L(x,y,t)$ for all
--      $x,y,t$, where $\widehat t$ denotes $t$ truncated to $[-M,M]$.
--   2. For every $x \in X$, $y \in Y$, the function $L(x,y,\cdot)$ has at least one global
--      minimizer in $[-M,M]$.
--
--   The lemma reduces the (a priori infinite-dimensional) question of whether clipping helps to a
--   one-dimensional statement about where a convex function attains its minimum, and it is the
--   tool the book uses throughout to show that the standard classification surrogates (hinge,
--   least-squares, truncated least-squares) can all be clipped at $M=1$.
--
--   **Formalization Note** Nonnegativity of `L` is not needed for either direction of the
--   argument and is dropped from the hypotheses (a strictly more general statement than the
--   book's literal typing `L : X × Y × ℝ → [0,∞)`, but not a different claim: the equivalence
--   holds verbatim for any convex real-valued `L(x,y,·)`). "Has a global minimizer in `[-M,M]`" is
--   stated directly as `∃ t0 ∈ [-M,M], ∀ t, L x y t0 ≤ L x y t`.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 34, Lemma 2.23

import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses

namespace SupportVectorMachines.LossFunctions

/-- Lemma 2.23 (Clipped convex losses), p. 34: let `L : X × Y × ℝ → [0,∞)` be a loss such that
`L(x,y,·)` is convex for every `x,y`, and let `M > 0`. Then `L` can be clipped at `M` if and only
if, for every `x, y`, the function `L(x,y,·) : ℝ → ℝ` has at least one global minimizer in
`[-M,M]`. -/
theorem lemma_2_23_clipped_convex_losses {X : Type*} (L : Loss X)
    (hconv : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (M : ℝ) (hM : 0 < M) :
    CanBeClipped L M ↔ ∀ x y, ∃ t0 ∈ Set.Icc (-M) M, ∀ t, L x y t0 ≤ L x y t := by sorry

end SupportVectorMachines.LossFunctions
