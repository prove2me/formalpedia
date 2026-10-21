-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P09_pointwise_limit_continuous
-- name    : QAlgorithms.Papers.Independent.Renew46.P09.pointwise_limit_continuous
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:03:25.263991+00:00
-- url     : https://prove2.me/theorems/504320ac-eadf-4637-b50e-252c604e9009
-- title:
--   Lemma 1.2: pointwise limits of continuous linear maps
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $V$ be a Hausdorff complete metrizable locally convex $\mathbb K$-vector space, and let $W$ be a metrizable topological $\mathbb K$-vector space. Suppose $\lambda_n:V\to W$ are continuous linear maps and $\lambda:V\to W$ satisfies
--
--   $$
--   \forall v\in V,\qquad \lim_{n\to\infty}\lambda_n(v)=\lambda(v).
--   $$
--
--   Then $\lambda$ is continuous. This provides continuity of a limit map from pointwise convergence, without normability of either space or completeness of $W$.
--
--   **Formalization Note** The compatible real scalar action expresses local convexity also in the complex case. A sequence indexed from zero is the reindexing of the source's positive-integer sequence.
-- source:
--   On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, PDF p. 3, Lemma 1.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P09

noncomputable section

open MeasureTheory Filter

open scoped Manifold ContDiff Topology

namespace QAlgorithms.Papers.Independent.Renew46.P09

/-- Lemma 1.2, PDF p.3: a pointwise limit of continuous linear maps on a
Frechet space is continuous. The target is only a metrizable topological vector
space, without a norm or completeness assumption. The real scalar action on V
is the restriction of its real or complex scalar action. Indexing from zero
reindexes the source's positive-integer sequence. -/
theorem pointwise_limit_continuous
    {K V W : Type*} [RCLike K]
    [AddCommGroup V] [Module K V] [Module ℝ V] [IsScalarTower ℝ K V]
    [UniformSpace V] [IsUniformAddGroup V] [TopologicalSpace.MetrizableSpace V] [CompleteSpace V]
    [ContinuousSMul K V] [LocallyConvexSpace ℝ V]
    [AddCommGroup W] [Module K W] [TopologicalSpace W] [TopologicalSpace.MetrizableSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul K W]
    (seq : ℕ → V →L[K] W) (lam : V → W)
    (hlim : ∀ v : V, Tendsto (fun n => seq n v) atTop (𝓝 (lam v))) :
    Continuous lam := by sorry

end QAlgorithms.Papers.Independent.Renew46.P09

end
