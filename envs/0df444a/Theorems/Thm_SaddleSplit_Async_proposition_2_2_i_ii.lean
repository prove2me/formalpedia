-- Prove2me | Theorems.Thm_SaddleSplit_Async_proposition_2_2_i_ii
-- name    : SaddleSplit.Async.proposition_2_2_i_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:26.792036+00:00
-- url     : https://prove2.me/theorems/73031958-07c6-4c4e-ac4e-e73d81cf6fc8
-- title:
--   Proposition 2.2(i)–(ii), p. 6 — the saddle operator is maximally monotone and its zero set is closed and convex
-- statement:
--   Consider the setting of Problem 1.1 and let $\boldsymbol{\mathcal S}:\mathbf X\to 2^{\mathbf X}$, $\mathbf X=\mathcal H\oplus\mathcal G\oplus\mathcal G\oplus\mathcal G$, be the saddle operator of Definition 2.1. Then:
--
--   1. $\boldsymbol{\mathcal S}$ is maximally monotone;
--   2. its zero set $\operatorname{zer}\boldsymbol{\mathcal S}=\{\mathbf x\in\mathbf X\mid \mathbf 0\in\boldsymbol{\mathcal S}\mathbf x\}$ is closed and convex.
--
--   $$\boldsymbol{\mathcal S}\ \text{maximally monotone},\qquad \operatorname{zer}\boldsymbol{\mathcal S}\ \text{closed and convex}.$$
--
--   Maximal monotonicity of $\boldsymbol{\mathcal S}$ is what makes its zero set a legitimate target for outer-approximation methods: the closed convex set $\operatorname{zer}\boldsymbol{\mathcal S}$ is the set Proposition 2.6 and Algorithm 3.4 approach.
--
--   **Formalization Note** All standing hypotheses [a]–[e] of Problem 1.1 are assumed (`prob.Hyp`); every space is a complete real inner product space.
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 6, Proposition 2.2(i)–(ii) (proof p. 7)

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Proposition 2.2(i)–(ii), p. 6: the saddle operator 𝓢 is maximally monotone, and zer 𝓢 is
closed and convex. -/
theorem proposition_2_2_i_ii {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp) :
    IsMaximalMonotone (saddleOp prob) ∧ IsClosed (zer (saddleOp prob)) ∧
      Convex ℝ (zer (saddleOp prob)) := by sorry

end SaddleSplit.Async
