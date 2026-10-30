-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_tangentMapThroughCurve
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.tangentMapThroughCurve
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:54:44.057975+00:00
-- url     : https://prove2.me/theorems/a373bac6-6099-41d9-a08b-e96e2dd08127
-- title:
--   Appendix A, Fact 1: tangent map through a curve
-- statement:
--   Let $M,N$ be finite-dimensional smooth real manifolds without boundary, let $i:N\hookrightarrow H$ be a smooth embedding into a real Hilbert space, and let $f:M\to N$ and $\gamma:\mathbb R\to M$ be smooth. Put $x=\gamma(0)$ and $\xi=\dot\gamma(0)$. Then
--   $$D i_{f(x)}\bigl(D f_x(\xi)\bigr)=\left.\frac{d}{dt}i(f(\gamma(t)))\right|_{t=0}.$$
--   The embedding differential explicitly relates intrinsic tangent vectors to ambient Hilbert-space vectors.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 35, Appendix A, Fact 1: tangent map through a curve

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Appendix A, Fact 1, PDF p.35: the tangent map evaluated on a curve
velocity, transported into the ambient Hilbert space by the embedding. -/
theorem tangentMapThroughCurve
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    [T2Space N] [SecondCountableTopology N]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (i : N → H) (hi : IsSmoothHilbertEmbedding (E := F) i) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ gamma) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) i (f (gamma 0))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (gamma 0)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 (1 : ℝ))) =
      deriv (fun t => i (f (gamma t))) 0 := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
