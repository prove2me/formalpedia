-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_gradientEnergyIdentity
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.gradientEnergyIdentity
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:48:00.206524+00:00
-- url     : https://prove2.me/theorems/21e351d1-80b4-427f-a13a-7da0db6d40e7
-- title:
--   §III.A: critical points and monotonicity
-- statement:
--   Let $M$ be a finite-dimensional smooth real manifold without boundary with a smooth positive-definite Riemannian metric $g$, and let $f:M\to\mathbb R$ be smooth. The constructed gradient satisfies $g_x(\operatorname{grad}f(x),v)=df_x(v)$, so $df_x=0$ exactly when $\operatorname{grad}f(x)=0$. For any gradient-ascent solution $\gamma$ on an open interval $I$,
--   $$\frac{d}{dt}f(\gamma(t))=g_{\gamma(t)}(\operatorname{grad}f,\dot\gamma)=g_{\gamma(t)}(\operatorname{grad}f,\operatorname{grad}f)=\|\operatorname{grad}f(\gamma(t))\|_{g}^2\ge0.$$
--   Consequently $f\circ\gamma$ is nondecreasing on $I$. This is a local statement and assumes no complete flow.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 9, §III.A: critical points and monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Critical/equilibrium correspondence and the full gradient energy
identity, PDF p.9. Solutions are local on an open interval; no completeness
assumption is imposed on a noncompact manifold. -/
theorem gradientEnergyIdentity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SecondCountableTopology M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M => TangentSpace 𝓘(ℝ, E) x))
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    (∀ x (v : TangentSpace 𝓘(ℝ, E) x),
      g.inner x (riemannianGradient g f x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x v) ∧
    (∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0 ↔ riemannianGradient g f x = 0) ∧
    ∀ (s : Set ℝ), IsOpen s → Convex ℝ s → ∀ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ gamma s →
      (∀ t ∈ s, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma t (1 : ℝ) =
        riemannianGradient g f (gamma t)) →
      (∀ t ∈ s,
        HasDerivAt (fun u => f (gamma u))
          (g.inner (gamma t) (riemannianGradient g f (gamma t))
            (riemannianGradient g f (gamma t))) t ∧
        0 ≤ g.inner (gamma t) (riemannianGradient g f (gamma t))
          (riemannianGradient g f (gamma t))) ∧
      MonotoneOn (fun t => f (gamma t)) s := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
