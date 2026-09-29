-- Prove2me | Theorems.Thm_Rudin_ch09_contraction_principle
-- name    : Rudin.ch09_contraction_principle
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:19:11.199642+00:00
-- url     : https://prove2.me/theorems/678b9b24-2449-4224-b926-113d96aa5454
-- title:
--   Theorem 9.23 — the contraction principle
-- statement:
--   If $X$ is a nonempty complete metric space and $\varphi : X \to X$ satisfies $d(\varphi(x),\varphi(y)) \le c\,d(x,y)$ for some constant $0 \le c < 1$, then $\varphi$ has exactly one fixed point.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 220, Definition 9.22 and Theorem 9.23

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.23 (the contraction principle): a contraction of a nonempty complete metric
space into itself has a unique fixed point. -/
theorem ch09_contraction_principle {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (φ : X → X) (c : ℝ) (hc : c < 1) (hc0 : 0 ≤ c)
    (hφ : ∀ x y : X, dist (φ x) (φ y) ≤ c * dist x y) :
    ∃! x : X, φ x = x := by sorry

end Rudin
