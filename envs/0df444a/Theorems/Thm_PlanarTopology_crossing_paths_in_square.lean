-- Prove2me | Theorems.Thm_PlanarTopology_crossing_paths_in_square
-- name    : PlanarTopology.crossing_paths_in_square
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T00:50:28.576189+00:00
-- url     : https://prove2.me/theorems/84567e46-2d81-4618-a538-9f95f6d456db
-- title:
--   Crossing paths in a square intersect
-- statement:
--   Two paths crossing a square, one from left to right and one from bottom to top, must meet.
--
--   Let $K=[-1,1]^2$. Let $f,g:[-1,1]\to K$ be continuous paths such that:
--
--   1. $f$ starts on the left side and ends on the right side: $f_1(-1)=-1$ and $f_1(1)=1$;
--   2. $g$ starts on the bottom side and ends on the top side: $g_2(-1)=-1$ and $g_2(1)=1$.
--
--   Then there are $s,t\in[-1,1]$ with
--   $$
--   f(s)=g(t).
--   $$
--
--   The lemma is the planar crossing principle used in shooting arguments. There, two one-parameter families of trajectories trace curves in a rectangle whose endpoints alternate around the boundary, and the curves must intersect. It is a standard consequence of the two-dimensional Brouwer fixed point theorem and needs neither injectivity of the paths nor the Jordan curve theorem.
--
--   **Formalization Note** The plane is modelled as $\mathbb R\times\mathbb R$. The paths are only required to be continuous on $[-1,1]$ and to take values in the closed square there.
-- source:
--   R. Maehara, The Jordan curve theorem via the Brouwer fixed point theorem, Amer. Math. Monthly 91 (1984), 641-643, Lemma (paths joining opposite sides of a square intersect).

import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace PlanarTopology

theorem crossing_paths_in_square (f g : ℝ → ℝ × ℝ)
    (hf : ContinuousOn f (Set.Icc (-1) 1)) (hg : ContinuousOn g (Set.Icc (-1) 1))
    (hfK : ∀ s ∈ Set.Icc (-1 : ℝ) 1, |(f s).1| ≤ 1 ∧ |(f s).2| ≤ 1)
    (hgK : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(g t).1| ≤ 1 ∧ |(g t).2| ≤ 1)
    (hf₀ : (f (-1)).1 = -1) (hf₁ : (f 1).1 = 1)
    (hg₀ : (g (-1)).2 = -1) (hg₁ : (g 1).2 = 1) :
    ∃ s ∈ Set.Icc (-1 : ℝ) 1, ∃ t ∈ Set.Icc (-1 : ℝ) 1, f s = g t := by sorry

end PlanarTopology
