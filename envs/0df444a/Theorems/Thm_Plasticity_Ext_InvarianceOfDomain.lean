-- Prove2me | Theorems.Thm_Plasticity_Ext_InvarianceOfDomain
-- name    : Plasticity.Ext.InvarianceOfDomain
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:01:19.585598+00:00
-- url     : https://prove2.me/theorems/277a3ec3-befb-4062-9f27-7a8b3447a444
-- title:
--   Invariance of domain in $\mathbb R^\iota$
-- statement:
--   Let $\iota$ be a finite set, $U\subseteq\mathbb R^\iota$ open, and $f\colon U\to\mathbb R^\iota$ continuous and injective. Then $f(U)$ is open.
--
--   It is used to show that a nonexpansive bijection of a ball between $c_{00}$ and $c_0$ cannot collapse a coordinate of a matched point.
--
--   **Formalization Note** $f$ is a function on all of $\mathbb R^\iota$, constrained on $U$ by `ContinuousOn` and `Set.InjOn`.
-- source:
--   L. E. J. Brouwer, Beweis der Invarianz des n-dimensionalen Gebietes, Math. Ann. 71 (1912), 305–313; proof from the Brouwer fixed-point theorem as in W. Kulpa, Poincaré and domain invariance theorem, Acta Univ. Carolin. Math. Phys. 39 (1998), 127–136

import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.ContinuousOn

namespace Plasticity.Ext
theorem InvarianceOfDomain {ι : Type*} [Fintype ι] (U : Set (ι → ℝ)) (hU : IsOpen U)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : ContinuousOn f U) (hinj : Set.InjOn f U) :
    IsOpen (f '' U) := by sorry
end Plasticity.Ext
