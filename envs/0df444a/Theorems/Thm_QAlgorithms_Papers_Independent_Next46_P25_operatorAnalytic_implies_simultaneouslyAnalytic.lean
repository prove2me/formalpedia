-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P25_operatorAnalytic_implies_simultaneouslyAnalytic
-- name    : QAlgorithms.Papers.Independent.Next46.P25.operatorAnalytic_implies_simultaneouslyAnalytic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:02:21.595324+00:00
-- url     : https://prove2.me/theorems/295a07f5-12b0-4357-a62f-2a004b6aae74
-- title:
--   Individual operator analyticity implies simultaneous analyticity on Baire algebras
-- statement:
--   Let $\mathbb K\in\{\mathbb R,\mathbb C\}$, let $\mathfrak g$ be a Hausdorff Baire topological Lie algebra with continuous bracket, and let $V$ be a normed $\mathbb K$-space. Let $\rho$ be a strongly continuous algebraic representation and let $v\in V$. Suppose that for every $x\in\mathfrak g$ there is $t_{x,v}>0$ for which $\sum_{n\ge0}\|\rho(x)^n v\|t_{x,v}^n/n!$ converges. Then there is one zero-neighborhood $U$ such that
--
--   $$
--   \sum_{n=0}^{\infty}\frac{\|\rho(x)^n v\|}{n!}<\infty
--   \qquad\text{for every }x\in U.
--   $$
--
--   The neighborhood may depend on $v$. No common individual radius is assumed, and no completeness of $V$ or Fréchet assumption on $\mathfrak g$ is imposed. This is the stated automatic simultaneous analyticity result.
-- source:
--   On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups, arXiv:1002.4792v2, PDF p. 17, Proposition 4.10

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25

noncomputable section

open Set Filter Topology

open scoped Classical ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Proposition 4.10, PDF p.17: Baire generality is retained. The radii
    before the implication depend on x and v; the conclusion gives one
    neighborhood for the fixed v. The proof's reference to joint continuity
    from Lemma 4.4 beyond the Frechet case is a recorded source issue. -/
theorem operatorAnalytic_implies_simultaneouslyAnalytic
    {K : Type u} [RCLike K]
    {g : Type v} [LieRing g] [LieAlgebra K g] [UniformSpace g]
    [IsUniformAddGroup g] [T2Space g] [ContinuousSMul K g]
    [BaireSpace g]
    {V : Type w} [NormedAddCommGroup V] [NormedSpace K V]
    (hBracket : Continuous (fun xy : g × g => ⁅xy.1, xy.2⁆))
    (rho : g →ₗ⁅K⁆ Module.End K V)
    (hStrong : StronglyContinuous (fun x v => rho x v))
    (v : V) (hIndividual : ∀ x : g, OperatorAnalytic (rho x) v) :
    SimultaneouslyAnalytic (fun x => rho x) v := by sorry

end QAlgorithms.Papers.Independent.Next46.P25

end
