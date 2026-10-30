-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_restrictionOfAmbientDerivative
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.restrictionOfAmbientDerivative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:55:17.38498+00:00
-- url     : https://prove2.me/theorems/dc927c23-a4d7-44f6-b99f-fc8b77b43964
-- title:
--   Appendix A, Fact 2: restriction of ambient derivative
-- statement:
--   Let $M,N$ be finite-dimensional smooth real manifolds smoothly embedded by $i:M\hookrightarrow H$ and $j:N\hookrightarrow H'$ in complete real Hilbert spaces. Let $F:H\to H'$ be smooth and assume $F(i(M))\subseteq j(N)$. Construct $f:M\to N$ uniquely by $j(f(x))=F(i(x))$. Then $f$ is smooth and
--   $$D j_{f(x)}\bigl(D f_x(v)\bigr)=D F_{i(x)}\bigl(D i_x(v)\bigr)\qquad(v\in T_xM).$$
--   This is restriction of the ambient derivative under the embedding identifications. The ambient spaces need not be finite-dimensional.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 35, Appendix A, Fact 2: restriction of ambient derivative

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Appendix A, Fact 2, PDF p.35: derivative of the constructed restriction,
through both embedding differentials. The ambient Hilbert spaces may be infinite-dimensional. -/
theorem restrictionOfAmbientDerivative
    {E Eprime : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Eprime] [NormedSpace ℝ Eprime] [FiniteDimensional ℝ Eprime]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace Eprime N] [IsManifold 𝓘(ℝ, Eprime) ∞ N]
    [T2Space N] [SecondCountableTopology N]
    {H Hprime : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Hprime] [InnerProductSpace ℝ Hprime] [CompleteSpace Hprime]
    (i : M → H) (j : N → Hprime) (hi : IsSmoothHilbertEmbedding (E := E) i)
    (hj : IsSmoothHilbertEmbedding (E := Eprime) j) (F : H → Hprime) (hF : ContDiff ℝ ∞ F)
    (himage : ∀ x, ∃ y, j y = F (i x)) :
    let f := embeddedRestriction i j F himage
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Eprime) ∞ f ∧
    (∀ x, j (f x) = F (i x)) ∧
    ∀ x (v : TangentSpace 𝓘(ℝ, E) x),
      mfderiv 𝓘(ℝ, Eprime) 𝓘(ℝ, Hprime) j (f x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Eprime) f x v) =
      fderiv ℝ F (i x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) i x v) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
