-- Prove2me | Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_front
-- name    : Plasticity.C0Sum.exists_blockEquiv_front
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:33.062297+00:00
-- url     : https://prove2.me/theorems/dacc0f9b-37ed-4d95-b604-759f1e4cf923
-- title:
--   The front: a nonexpansive bijection of $c_0$-sum balls carries a non-parallelogram planar source block into one planar target block, with killable completions
-- statement:
--   Let $(E_i)_{i\in I}$ be a family of real normed spaces and $(E'_k)_{k\in K}$ a family of real normed spaces of dimension $1$ or $2$, over arbitrary index sets, and let $X=c_0(I;E_i)$ and $Y=c_0(K;E'_k)$ carry the supremum block norms, with closed unit balls $B_X$ and $B_Y$.
--   Write $x_i$ for the block of $x$ at $i$, and say that $x$ is supported in block $i$ if $x_k=0$ for every $k\ne i$.
--   Let $F\colon X\to Y$ map $B_X$ bijectively onto $B_Y$ and be $1$-Lipschitz on $B_X$.
--   Let $i\in I$ be such that $E_i$ has dimension $2$ and its closed unit ball $D$ has more than four extreme points.
--   Then there is $j\in K$ with $\dim E'_j=2$ such that the following hold.
--
--   - Every $x\in B_X$ supported in block $i$ has $F(x)$ supported in block $j$.
--   - For every $a\in D$ with $a\ne0$ there are $c_1,c_2\in D$ with $$D\subseteq B(a,1)\cup B(c_1,1)\cup B(c_2,1),$$ where $B(c,1)$ is the closed ball of radius $1$ about $c$ in $E_i$, and a point $u$ of the closed unit ball of $E'_j$ with $\|u-F(x)_j\|>1$ for every $x\in B_X$ supported in block $i$ with $x_i=c_1$ or $x_i=c_2$.
--
--   No hypothesis is placed on the source blocks other than $E_i$.
-- source:
--   This repository: claim CUB103 (claims/cub.md), Propositions 3.4–3.5 in expositions/c0_planes_front.md §3, for one planar source block, with genericity in place of tangent points and Lemma 3.3

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.C0Sum
theorem exists_blockEquiv_front {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (F : c0Sum E → c0Sum E')
    (hbij : Set.BijOn F (Metric.closedBall 0 1) (Metric.closedBall 0 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall 0 1))
    (i : ι) (hi : Module.finrank ℝ (E i) = 2)
    (hpar : 4 < (Set.extremePoints ℝ (Metric.closedBall (0 : E i) 1)).encard) :
    ∃ j : κ, Module.finrank ℝ (E' j) = 2 ∧
      (∀ x ∈ Metric.closedBall (0 : c0Sum E) 1, (∀ k ≠ i, (x : lp E ⊤) k = 0) →
        ∀ m ≠ j, (F x : lp E' ⊤) m = 0) ∧
      ∀ a : E i, a ≠ 0 → ‖a‖ ≤ 1 → ∃ c₁ c₂ : E i, ‖c₁‖ ≤ 1 ∧ ‖c₂‖ ≤ 1 ∧
        Metric.closedBall (0 : E i) 1 ⊆
          Metric.closedBall a 1 ∪ Metric.closedBall c₁ 1 ∪ Metric.closedBall c₂ 1 ∧
        ∃ u : E' j, ‖u‖ ≤ 1 ∧ ∀ x ∈ Metric.closedBall (0 : c0Sum E) 1,
          (∀ k ≠ i, (x : lp E ⊤) k = 0) → ((x : lp E ⊤) i = c₁ ∨ (x : lp E ⊤) i = c₂) →
            1 < ‖u - (F x : lp E' ⊤) j‖ := by sorry
end Plasticity.C0Sum
