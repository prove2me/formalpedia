-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_convex_mixtures_uniform_equivalence
-- name    : QAlgorithms.Papers.Independent.Support21.P17.convex_mixtures_uniform_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:45:53.096448+00:00
-- url     : https://prove2.me/theorems/8c626721-af3e-4caf-9ea6-bc3d5c353ba3
-- title:
--   Uniform equivalence of convex mixtures
-- statement:
--   Let $S_1,S_2:B(H)\to B(K)$ be channels, and let $0<\lambda,\lambda'<1$. Put $T=\lambda S_1+(1-\lambda)S_2$ and $T'=\lambda'S_1+(1-\lambda')S_2$. With the source's constants $c=[\lambda(1-\lambda)]^{-1}$ and $c'=[\lambda'(1-\lambda')]^{-1}$, one has
--
--   $$c,c'>1,\qquad T'\le cT,\qquad T\le c'T'.$$
--
--   For normal CP maps, define $S\equiv_u T$ by mutual CP domination with constants greater than one. This relation is an equivalence relation, and the displayed mixtures are uniformly equivalent. This is a particular construction, not a claim about arbitrary channel pairs.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 12, §4, unnumbered: uniformly equivalent convex mixtures

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Section 4, PDF p.12: convex mixtures are mutually dominated with the printed
constants. Uniform equivalence is also an equivalence relation on normal CP maps. -/
theorem convex_mixtures_uniform_equivalence (H K : SeparableHilbertSpace) :
    (∀ (S1 S2 : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K), IsUnitalNormalCP S1 → IsUnitalNormalCP S2 →
      ∀ l r : ℝ, 0 < l → l < 1 → 0 < r → r < 1 →
      let T := (l : ℂ) • S1 + ((1 - l : ℝ) : ℂ) • S2
      let U := (r : ℂ) • S1 + ((1 - r : ℝ) : ℂ) • S2
      1 < (l * (1 - l))⁻¹ ∧ 1 < (r * (1 - r))⁻¹ ∧
      CompletelyDominated U ((((l * (1 - l))⁻¹ : ℝ) : ℂ) • T) ∧
      CompletelyDominated T ((((r * (1 - r))⁻¹ : ℝ) : ℂ) • U) ∧ UniformlyEquivalent T U) ∧
    Equivalence (fun S T : {T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K //
      IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T} => UniformlyEquivalent S.val T.val) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
