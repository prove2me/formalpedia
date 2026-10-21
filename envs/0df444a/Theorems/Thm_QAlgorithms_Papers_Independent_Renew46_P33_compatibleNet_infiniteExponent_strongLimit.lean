-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P33_compatibleNet_infiniteExponent_strongLimit
-- name    : QAlgorithms.Papers.Independent.Renew46.P33.compatibleNet_infiniteExponent_strongLimit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:04:28.137823+00:00
-- url     : https://prove2.me/theorems/e58604c3-b66d-4163-af8c-3acd1d73b2c8
-- title:
--   Compatible bounded operator nets have a strong limit (corrected infinite endpoint)
-- statement:
--   Let $M\subseteq B(H)$ be a von Neumann algebra on an arbitrary complex Hilbert space. Let $I$ be a nonempty directed partially ordered set, let $\xi_i\in M$, and let $p_i\in M$ be orthogonal projections. Suppose that $\xi_i=\xi_i p_i$, that $\xi_jp_i=\xi_i$ whenever $i<j$, and that $\|\xi_i\|\le C$ for a finite real bound $C$, uniformly in $i$. Then some $\xi\in M$ satisfies
--
--   $$
--   \|\xi\|\le C,\qquad \xi_i v\longrightarrow\xi v\quad(v\in H),\qquad \xi_i=\xi p_i\quad(i\in I).
--   $$
--
--   This is the bounded-algebra endpoint of compatible-column convergence. The projections themselves are not required to increase.
--
--   **Source correction.** The printed claim that Lemma 1.4 still holds at infinity is read with strong operator convergence. Norm convergence is false for finite-rank coordinate projections tending strongly to the identity on an infinite-dimensional Hilbert space. The endpoint argument on PDF p.6 explicitly uses a strong limit. Independent moderation of this correction remains pending.
-- source:
--   Noncommutative Lp modules, arXiv:math/0301044v2, PDF p. 5, unnumbered-infinite-exponent-compatible-net

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P33

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Renew46.P33

/-- The unnumbered endpoint following Lemma 1.4, PDF p.5, read together with
(1.3) on p.4 and the explicit endpoint argument on p.6.
Source correction: the printed assertion that Lemma 1.4 "still holds" at
infinity must use strong operator convergence instead of norm convergence.
For finite-rank coordinate projections on ell2, the hypotheses hold but the
operator norm distance to the identity stays one. The corrected strong limit
retains every restriction identity and the uniform operator norm bound.
The directed index type is nonempty; the projections need not be increasing.
No sigma-finiteness or separability hypothesis is imposed. -/
theorem compatibleNet_infiniteExponent_strongLimit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H)
    {I : Type*} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    (xi proj : I → H →L[ℂ] H)
    (hxi : ∀ i, xi i ∈ M)
    (hproj : ∀ i, proj i ∈ M ∧ IsStarProjection (proj i))
    (hsupport : ∀ i, xi i = xi i * proj i)
    (hcompat : ∀ i j, i < j → xi j * proj i = xi i)
    (C : ℝ) (hbound : ∀ i, ‖xi i‖ ≤ C) :
    ∃ limit : H →L[ℂ] H,
      limit ∈ M ∧ ‖limit‖ ≤ C ∧
      (∀ v : H, Tendsto (fun i => xi i v) atTop (𝓝 (limit v))) ∧
      (∀ i, xi i = limit * proj i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P33
