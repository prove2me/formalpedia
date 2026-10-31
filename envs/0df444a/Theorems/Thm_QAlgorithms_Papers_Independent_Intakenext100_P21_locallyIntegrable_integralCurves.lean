-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P21_locallyIntegrable_integralCurves
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P21.locallyIntegrable_integralCurves
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:44:27.126994+00:00
-- url     : https://prove2.me/theorems/01320d86-f806-4eab-9f2c-2b915612d581
-- title:
--   Integral curves and uniqueness for locally integrable vector fields
-- statement:
--   Let $M$ be a Hausdorff smooth manifold modeled on a Hausdorff locally convex real space, with smoothness understood in the Bastiani calculus. Let $X$ be a smooth vector field which is the velocity field of a smooth local flow.
--
--   1. Every flow line of a local flow with velocity $X$ is an integral curve of $X$.
--   2. Integral curves of $X$ on the same open interval containing zero agree if their initial values agree.
--   3. Two local flows on the same domain with the same velocity field agree on that domain.
--   4. Through every $m\in M$ there is a unique maximal integral curve $\gamma_m:I_m\to M$ with $0\in I_m$ and $\gamma_m(0)=m$. Every other integral curve through $m$ is its restriction:
--
--   $$
--   I\subseteq I_m,\qquad \gamma(t)=\gamma_m(t)\quad(t\in I).
--   $$
--
--   The result supplies uniqueness under local integrability without asserting uniqueness for general locally convex ordinary differential equations.
-- source:
--   Integrability of unitary representations on reproducing kernel spaces, arXiv:1406.2681v3, PDF p. 7, Lemma 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P21

namespace QAlgorithms.Papers.Independent.Intakenext100.P21

open Set Filter Topology

open QAlgorithms.Papers.Independent.Claimed50.P22 (BastianiSmoothOn BastianiAtlas)

open QAlgorithms.Papers.Independent.Next46.P15 (HasDirectionalDerivative directionalDerivative)

attribute [local instance] Classical.propDecidable

universe u v w

section Manifolds

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

variable [LocallyConvexSpace ℝ E] [T2Space E] [T2Space M]

/-- Lemma 2.5, PDF pp. 7--8, all four clauses. In (ii) the initial
values are equal, as explicitly used in the proof on p. 8; the printed
sentence omits this condition. Uniqueness is equality on curve/flow domains,
not equality of irrelevant off-domain representatives. -/
theorem locallyIntegrable_integralCurves
    (hAtlas : BastianiAtlas (E := E) (M := M))
    (X : CoordinateField E M) (hX : IsLocallyIntegrable X) :
    (∀ P : FlowData M, IsLocalFlow (E := E) P → HasVelocityField P X →
      ∀ m : M, IsIntegralCurve X {t | (t, m) ∈ P.domain} (fun t => P.value t m)) ∧
    (∀ (I : Set ℝ) (gamma eta : ℝ → M),
      IsIntegralCurve X I gamma → IsIntegralCurve X I eta → gamma 0 = eta 0 →
      ∀ t ∈ I, gamma t = eta t) ∧
    (∀ (P Q : FlowData M) (Z : CoordinateField E M),
      IsLocalFlow (E := E) P → IsLocalFlow (E := E) Q →
      HasVelocityField P Z → HasVelocityField Q Z → P.domain = Q.domain →
      ∀ t m, (t, m) ∈ P.domain → P.value t m = Q.value t m) ∧
    (∀ m : M, ∃ (I : Set ℝ) (gamma : ℝ → M),
      IsMaximalIntegralCurve X I gamma ∧ gamma 0 = m ∧
      (∀ (J : Set ℝ) (eta : ℝ → M), IsIntegralCurve X J eta → eta 0 = m →
        CurveExtends J eta I gamma) ∧
      (∀ (J : Set ℝ) (eta : ℝ → M), IsMaximalIntegralCurve X J eta → eta 0 = m →
        I = J ∧ ∀ t ∈ I, gamma t = eta t)) := by sorry

end Manifolds

end QAlgorithms.Papers.Independent.Intakenext100.P21
