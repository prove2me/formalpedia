-- Prove2me | Theorems.Thm_RegretMatching_Approach_support_negOrthant
-- name    : RegretMatching.Approach.support_negOrthant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:58.314944+00:00
-- url     : https://prove2.me/theorems/37be8c05-c246-4076-bfcc-1f3f67ab6dba
-- title:
--   §3, proof of THEOREM A, p. 1136 — the support function of ℝ^L_− is 0 on ℝ^L_+ and +∞ otherwise
-- statement:
--   Let $L$ be a finite set and $\mathbb R^L_-=\{x\in\mathbb R^L: x\le0\}$ the nonpositive orthant. Its support function $w(\lambda)=\sup\{\lambda\cdot c: c\in\mathbb R^L_-\}$ satisfies
--   $$w(\lambda)=0\ \text{ for }\lambda\in\mathbb R^L_+,\qquad w(\lambda)=+\infty\ \text{ otherwise.}$$
--   Precisely:
--   1. if every coordinate of $\lambda$ is nonnegative, then $0$ is the least upper bound of $\{\lambda\cdot c: c\le 0\}$;
--   2. if some coordinate of $\lambda$ is negative, then $\{\lambda\cdot c: c\le0\}$ is unbounded above.
--
--   Consequently only $\lambda\in\mathbb R^L_+$ need to be considered in Blackwell's condition (3.2) for $\mathbb R^L_-$.
--
--   **Formalization Note.** The value $+\infty$ is expressed as "not bounded above" and the value $0$ as a least upper bound, so no real-valued supremum (which Lean sets to $0$ on unbounded sets) is used.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1136, proof of THEOREM A

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Approach

theorem support_negOrthant
    {L : Type} [Fintype L] (lam : EuclideanSpace ℝ L) :
    ((∀ l, 0 ≤ lam l) → IsLUB ((fun c => inner ℝ lam c) '' negOrthant L) 0) ∧
      ((∃ l, lam l < 0) → ¬ BddAbove ((fun c => inner ℝ lam c) '' negOrthant L)) := by sorry

end RegretMatching.Approach
