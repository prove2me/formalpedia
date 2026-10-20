-- Prove2me | Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_three_balls
-- name    : Plasticity.C0Sum.exists_blockEquiv_three_balls
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:32.102751+00:00
-- url     : https://prove2.me/theorems/b40ecb84-40b9-447a-b938-c16835d2ca9b
-- title:
--   Three unit balls covering the ball of a $c_0$ sum of lines and planes: the configurations that resist killing
-- statement:
--   Let $(E'_k)_{k\in K}$ be a family of real normed spaces over an arbitrary index set, each of dimension $1$ or $2$, and let $Y=c_0(K;E'_k)$ carry the supremum block norm, with closed unit ball $B_Y$; write $q_k$ for the block of $q\in Y$ at $k$.
--   Let $q_0,q_1,q_2\in Y$ with $q_1\ne0$, $q_2\ne0$ and $$B_Y\subseteq B(q_0,1)\cup B(q_1,1)\cup B(q_2,1),$$ where $B(c,1)$ is the closed ball of radius $1$ about $c$ in $Y$, and let $m\ne m'$ be indices with $(q_0)_m\ne0$ and $(q_0)_{m'}\ne0$.
--   Then at least one of the following holds.
--
--   1. There are $n\in K$ and $\mu>0$ with $(q_1)_k=(q_2)_k=0$ for every $k\ne n$ and $(q_2)_n=-\mu\,(q_1)_n$.
--   2. There are $q\in\{q_1,q_2\}$, $n\in\{m,m'\}$ and $t\in\mathbb R$ with $q_k=0$ for every $k\ne n$ and $q_n=t\,(q_0)_n$.
--
--   In the second alternative $t\ne0$, since $q\ne0$.
-- source:
--   This repository: claim CUB93 (claims/cub.md), Lemma 2.2 in expositions/c0_disc_polygon_mixtures.md §2, in a generic form that lists the configurations resisting the kill instead of excluding tangent points

import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.C0Sum
theorem exists_blockEquiv_three_balls {κ : Type*}
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (q₀ q₁ q₂ : c0Sum E') (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hcov : Metric.closedBall (0 : c0Sum E') 1 ⊆
      Metric.closedBall q₀ 1 ∪ Metric.closedBall q₁ 1 ∪ Metric.closedBall q₂ 1)
    (m m' : κ) (hmm' : m ≠ m') (hm : (q₀ : lp E' ⊤) m ≠ 0) (hm' : (q₀ : lp E' ⊤) m' ≠ 0) :
    (∃ n : κ, (∀ k ≠ n, (q₁ : lp E' ⊤) k = 0 ∧ (q₂ : lp E' ⊤) k = 0) ∧
        ∃ μ : ℝ, 0 < μ ∧ (q₂ : lp E' ⊤) n = -(μ • (q₁ : lp E' ⊤) n)) ∨
      ∃ q ∈ ({q₁, q₂} : Set (c0Sum E')), ∃ n ∈ ({m, m'} : Set κ),
        (∀ k ≠ n, (q : lp E' ⊤) k = 0) ∧ ∃ t : ℝ, (q : lp E' ⊤) n = t • (q₀ : lp E' ⊤) n := by sorry
end Plasticity.C0Sum
