-- Prove2me | Theorems.Thm_Plasticity_Topology_exists_closedBall_model_of_convex_compact
-- name    : Plasticity.Topology.exists_closedBall_model_of_convex_compact
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:52.88698+00:00
-- url     : https://prove2.me/theorems/f67df7e4-2f51-4fae-8758-f9f2ceace022
-- title:
--   A nonempty compact convex set with finite-dimensional span is a closed ball in its direction space
-- statement:
--   Let $C$ be a nonempty compact convex subset of a real normed space whose affine hull is finite-dimensional, with direction space $V=\operatorname{span}(C-C)$. There are continuous maps $\varphi\colon V\to E$ and $\psi\colon E\to V$ such that $\varphi$ maps the closed unit ball of $V$ onto $C$ with inverse $\psi$ on $C$, and $\varphi(z)$ lies in the relative boundary of $C$ exactly when $\|z\|=1$.
-- source:
--   Radial projection from a relative-interior point; Mathlib's gauge rescaling (Mathlib/Analysis/Convex/GaugeRescale.lean)

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Intrinsic

namespace Plasticity.Topology
theorem exists_closedBall_model_of_convex_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E)
    (hcpt : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hfin : FiniteDimensional ℝ (vectorSpan ℝ C)) :
    ∃ φ : vectorSpan ℝ C → E, ∃ ψ : E → vectorSpan ℝ C, Continuous φ ∧ Continuous ψ ∧
      (∀ z : vectorSpan ℝ C, ‖z‖ ≤ 1 →
        φ z ∈ C ∧ ψ (φ z) = z ∧ (φ z ∈ intrinsicFrontier ℝ C ↔ ‖z‖ = 1)) ∧
      ∀ y ∈ C, ‖ψ y‖ ≤ 1 ∧ φ (ψ y) = y := by sorry
end Plasticity.Topology
