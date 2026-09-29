-- Prove2me | Theorems.Thm_Rudin_ch07_nowhere_differentiable
-- name    : Rudin.ch07_nowhere_differentiable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T00:07:52.164539+00:00
-- url     : https://prove2.me/theorems/0f4f0864-f13b-43dd-af99-02d8b772221f
-- title:
--   Theorem 7.18 — a continuous nowhere differentiable function
-- statement:
--   There exists a real continuous function on the real line which is differentiable at no point.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, p. 154, Theorem 7.18

import Mathlib
import Definitions.Def_Rudin_ch07_families

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 7.18: there exists a real continuous function on the real line which is
differentiable at no point. -/
theorem ch07_nowhere_differentiable :
    ∃ f : ℝ → ℝ, Continuous f ∧ ∀ x : ℝ, ¬ DifferentiableAt ℝ f x := by sorry

end Rudin
