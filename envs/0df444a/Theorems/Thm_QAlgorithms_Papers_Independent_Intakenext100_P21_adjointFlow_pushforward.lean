-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P21_adjointFlow_pushforward
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P21.adjointFlow_pushforward
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:47:00.634024+00:00
-- url     : https://prove2.me/theorems/b44d6f6f-a19e-42c3-8cae-dfda23fe4695
-- title:
--   Equivariance of an infinitesimal action under a local flow
-- statement:
--   Let $M$ be a Hausdorff smooth manifold modeled on a Hausdorff locally convex real space, with smoothness understood in the Bastiani calculus. Let $\mathfrak g$ be a Hausdorff locally convex real Lie algebra with continuous bracket. Assume it is ad-integrable: every linear vector field $y\mapsto[x,y]$ generates a global flow. Write $e^{t\operatorname{ad}x}y$ for that flow at time $t$. Let $\beta:\mathfrak g\to\mathcal V(M)$ be a Lie algebra homomorphism with smooth joint evaluation $(y,m)\mapsto\beta(y)(m)$. Fix $x$ for which $\beta(x)$ is locally integrable, with maximal flow $\Phi^x$. Then for all $y\in\mathfrak g$ and $t\in\mathbb R$,
--
--   $$
--   (\Phi^x_{-t})_*\beta(y)=\left.\beta(e^{t\operatorname{ad}x}y)\right|_{M_t}.
--   $$
--
--   Only the selected field $\beta(x)$ needs to be locally integrable. This transports the adjoint flow into the geometric action without using a bounded-operator exponential on a general locally convex space.
-- source:
--   Integrability of unitary representations on reproducing kernel spaces, arXiv:1406.2681v3, PDF p. 11, Lemma 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P21

namespace QAlgorithms.Papers.Independent.Intakenext100.P21

open Set Filter Topology

open QAlgorithms.Papers.Independent.Claimed50.P22 (BastianiSmoothOn BastianiAtlas)

open QAlgorithms.Papers.Independent.Next46.P15 (HasDirectionalDerivative directionalDerivative)

attribute [local instance] Classical.propDecidable

universe u v w

section AdjointFlows

variable {A : Type u} [TopologicalSpace A] [LieRing A] [Module ℝ A]

variable [LieAlgebra ℝ A]

variable {E : Type v} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

variable {M : Type w} [TopologicalSpace M] [ChartedSpace E M]

/-- Lemma 3.4, PDF pp. 11--12, formula (3.1): the pushforward by
Phi[-t] equals beta(e^(t ad x)y) on M_t. Only beta(x) is assumed
locally integrable. The sign and the time domain follow the displayed formula. -/
theorem adjointFlow_pushforward
    [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [LocallyConvexSpace ℝ A] [T2Space A]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] [T2Space M]
    (hBracket : Continuous (fun p : A × A => ⁅p.1, p.2⁆))
    (hAd : IsAdIntegrable (A := A))
    (hAtlas : BastianiAtlas (E := E) (M := M))
    (beta : A →ₗ[ℝ] CoordinateField E M) (hBeta : IsSmoothInfinitesimalAction beta)
    (x : A) (hx : IsLocallyIntegrable (beta x)) :
    ∀ y : A, ∀ t : ℝ, ∀ c ∈ atlas E M, ∀ m ∈ c.source,
      (t, m) ∈ (maximalFlow (beta x)).domain →
        pullbackCoordinate (maximalFlow (beta x)) (beta y) t c m =
          beta (adjointEvolution x y t) c m := by sorry

end AdjointFlows

end QAlgorithms.Papers.Independent.Intakenext100.P21
