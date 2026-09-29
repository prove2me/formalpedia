-- Prove2me | Theorems.Thm_WhitneyEmbedding_injective_immersion_of_blockwise_immersions
-- name    : WhitneyEmbedding.injective_immersion_of_blockwise_immersions
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T15:23:56.7218+00:00
-- url     : https://prove2.me/theorems/e560623b-e18e-4d47-8e18-f70472018660
-- title:
--   Gluing blockwise injective immersions along the level sets of a smooth function
-- statement:
--   Let $M$ be a smooth $n$-manifold and let $r : M \to \mathbb{R}$ be smooth. Slice $M$ by the level sets of $r$ into the closed blocks
--   $$B_j \;=\; r^{-1}\big([\,j-1,\; j+1\,]\big), \qquad j \in \mathbb{Z}.$$
--   Assume that for every $j$ there is a smooth map $g_j : M \to \mathbb{R}^m$, with one and the same target dimension $m$, which is injective on $B_j$ and whose differential is injective at every point of $B_j$. Then $M$ admits a global smooth injective immersion into a Euclidean space: there are $N$ and a smooth $e : M \to \mathbb{R}^N$ with $e$ injective and $de_x$ injective for every $x \in M$.
--
--   The construction is a two-colouring of the blocks. Fix $\chi : \mathbb{R} \to \mathbb{R}$ smooth, nonnegative, positive exactly on $(-1,1)$ and vanishing outside it, and set
--   $$A(x) \;=\; \Big( \sum_{k \in \mathbb{Z}} \chi\big(r(x)-2k\big)\, g_{2k}(x), \; \sum_{k \in \mathbb{Z}} \chi\big(r(x)-2k\big) \Big), \qquad
--   A'(x) \;=\; \Big( \sum_{k \in \mathbb{Z}} \chi\big(r(x)-2k-1\big)\, g_{2k+1}(x), \; \sum_{k \in \mathbb{Z}} \chi\big(r(x)-2k-1\big) \Big),$$
--   both valued in $\mathbb{R}^{m+1}$; the sums are locally finite because near a given point only the finitely many terms with $2k$ close to $r(x)$ are nonzero, so both maps are smooth. Put
--   $$e \;=\; (A, A', r) : M \to \mathbb{R}^{2m+3}.$$
--
--   For injectivity, suppose $e(x) = e(y)$; in particular $t := r(x) = r(y)$. The even intervals $(2k-1,2k+1)$ cover every $t$ that is not an odd integer, and the odd intervals $(2k,2k+2)$ cover every $t$ that is not an even integer, so $t$ lies in some interval of one of the two families, say the even one, around $2k$. Then $\chi(t-2k) = c > 0$ while all other terms of the even sum vanish at both points, so the last coordinate of $A$ gives $c$ at both points and the first block gives $c\,g_{2k}(x) = c\,g_{2k}(y)$, whence $g_{2k}(x) = g_{2k}(y)$. Since $x,y \in B_{2k}$ and $g_{2k}$ is injective there, $x = y$.
--
--   For the immersion property, let $v \in T_xM$ with $de_x(v) = 0$. The last coordinate gives $dr_x(v) = 0$, and on the open set $r^{-1}\big((2k-1,2k+1)\big)$ containing $x$ the map $A$ equals $\big(\chi(r-2k)\,g_{2k}, \chi(r-2k)\big)$, so differentiating and using $dr_x(v)=0$ leaves $\chi(t-2k)\, d(g_{2k})_x(v) = 0$ with $\chi(t-2k) > 0$. Hence $d(g_{2k})_x(v) = 0$ and $v = 0$ because $g_{2k}$ is an immersion at $x \in B_{2k}$.
--
--   No properness of $r$ is required for this gluing step; properness is what one uses upstream, to know that the blocks $B_j$ are compact so that blockwise immersions exist.
-- source:
--   Zuoqin Wang, Lecture 9: The Whitney Embedding Theorem, Theorem 2.1 and its proof, printed p.5, https://www.math.wustl.edu/~victor/classes/pmf/WhitEmb-Lec09.pdf

import Mathlib
open Function Filter Module Set Topology
open scoped Manifold ContDiff

theorem WhitneyEmbedding.injective_immersion_of_blockwise_immersions (n m : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (r : M → ℝ) (hr : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ r)
    (g : ℤ → M → EuclideanSpace ℝ (Fin m))
    (hg : ∀ j, ContMDiff (𝓡 n) (𝓡 m) ∞ (g j))
    (hginj : ∀ j : ℤ, InjOn (g j) (r ⁻¹' (Set.Icc ((j : ℝ) - 1) ((j : ℝ) + 1))))
    (hgimm : ∀ j : ℤ, ∀ x ∈ r ⁻¹' (Set.Icc ((j : ℝ) - 1) ((j : ℝ) + 1)),
      Injective (mfderiv (𝓡 n) (𝓡 m) (g j) x)) :
    ∃ (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N)),
      ContMDiff (𝓡 n) (𝓡 N) ∞ e ∧ Injective e ∧
      (∀ x, Injective (mfderiv (𝓡 n) (𝓡 N) e x)) := by sorry
