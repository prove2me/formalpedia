-- Prove2me | Theorems.Thm_Plasticity_C0Sum_exists_blockEquiv_two_balls
-- name    : Plasticity.C0Sum.exists_blockEquiv_two_balls
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:37.053982+00:00
-- url     : https://prove2.me/theorems/4a789848-e2c4-4d31-acee-9c02cddf5344
-- title:
--   Two unit balls covering the ball of a $c_0$ sum of lines and planes have centres in one common block, opposite there
-- statement:
--   Let $(E'_k)_{k\in K}$ be a family of real normed spaces over an arbitrary index set, each of dimension $1$ or $2$, and let $Y=c_0(K;E'_k)$ carry the supremum block norm, with closed unit ball $B_Y$; write $p_k$ for the block of $p\in Y$ at $k$.
--   Let $p,q\in Y$ be nonzero with $$B_Y\subseteq B(p,1)\cup B(q,1),$$ where $B(c,1)$ is the closed ball of radius $1$ about $c$ in $Y$.
--   Then there are $m\in K$ and $\mu>0$ such that $p_k=q_k=0$ for every $k\ne m$ and $$q_m=-\mu\,p_m.$$
--   So $p$ and $q$ are supported in one common block, where they are opposite multiples of each other.
-- source:
--   This repository: claims CUB93 and CUB99(1) (claims/cub.md), the support separation of CUB93 Lemma 2.1 (expositions/c0_disc_polygon_mixtures.md §2) with the two-translate lemma CUB99(1) in the block (expositions/c0_one_general_plane.md §2.2), as used in Lemma 3.1 of expositions/c0_planes_front.md §3 and in expositions/c0_planes_with_scalars.md §2

import Definitions.Def_Plasticity_C0Sum
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.C0Sum
theorem exists_blockEquiv_two_balls {κ : Type*}
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE' : ∀ k, Module.finrank ℝ (E' k) = 1 ∨ Module.finrank ℝ (E' k) = 2)
    (p q : c0Sum E') (hp : p ≠ 0) (hq : q ≠ 0)
    (hcov : Metric.closedBall (0 : c0Sum E') 1 ⊆ Metric.closedBall p 1 ∪ Metric.closedBall q 1) :
    ∃ m : κ, (∀ k ≠ m, (p : lp E' ⊤) k = 0 ∧ (q : lp E' ⊤) k = 0) ∧
      ∃ μ : ℝ, 0 < μ ∧ (q : lp E' ⊤) m = -(μ • (p : lp E' ⊤) m) := by sorry
end Plasticity.C0Sum
