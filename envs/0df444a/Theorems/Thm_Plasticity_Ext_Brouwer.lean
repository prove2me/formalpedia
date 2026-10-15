-- Prove2me | Theorems.Thm_Plasticity_Ext_Brouwer
-- name    : Plasticity.Ext.Brouwer
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:01:19.824875+00:00
-- url     : https://prove2.me/theorems/52ab850f-37ac-425e-abcd-f86b18e50315
-- title:
--   Brouwer fixed-point theorem for the cube $[-1,1]^\iota$
-- statement:
--   Let $\iota$ be a finite set and $f$ a continuous map of the cube $[-1,1]^\iota\subset\mathbb R^\iota$ into itself. Then $f$ has a fixed point.
--
--   It is the input for invariance of domain.
--
--   **Formalization Note** The cube is the order interval `Set.Icc (-1) 1` in `ι → ℝ`; $f$ is a function on all of $\mathbb R^\iota$, constrained on the cube by `ContinuousOn` and `Set.MapsTo`. A proof exists on this platform for the unit cube $[0,1]^n$ in another environment (`fixed_point_unit_cube`, via cubical Sperner).
-- source:
--   L. E. J. Brouwer, Über Abbildung von Mannigfaltigkeiten, Math. Ann. 71 (1912), 97–115; formal proof via cubical Sperner after harfe/fixed-point-theorems-lean4 (MIT licence)

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Topology.ContinuousOn

namespace Plasticity.Ext
theorem Brouwer {ι : Type*} [Fintype ι] (f : (ι → ℝ) → (ι → ℝ))
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (hmaps : Set.MapsTo f (Set.Icc (-1) 1) (Set.Icc (-1) 1)) :
    ∃ x ∈ Set.Icc (-1 : ι → ℝ) 1, f x = x := by sorry
end Plasticity.Ext
