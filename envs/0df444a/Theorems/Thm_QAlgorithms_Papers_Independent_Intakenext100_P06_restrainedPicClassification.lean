-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_restrainedPicClassification
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.restrainedPicClassification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:47:39.644989+00:00
-- url     : https://prove2.me/theorems/8396dd25-8905-4e5b-b05f-f036d0cea376
-- title:
--   Classification of restrained Pic-categories
-- statement:
--   Let $\mathcal C$ and $\mathcal D$ be symmetric monoidal Gr-categories whose self-symmetries are identity maps. Write $\pi_0(\mathcal C)$ and $\pi_0(\mathcal D)$ for their groups of object isomorphism classes under tensor, and $I_{\mathcal C},I_{\mathcal D}$ for their units. Then
--
--   $$
--   \mathcal C\simeq_{\otimes,\mathrm{sym}}\mathcal D
--   \iff
--   \bigl(\pi_0(\mathcal C)\cong\pi_0(\mathcal D)\bigr)
--   \ \text{and}\
--   \bigl(\operatorname{Aut}(I_{\mathcal C})\cong\operatorname{Aut}(I_{\mathcal D})\bigr).
--   $$
--
--   Both displayed groups are intrinsically abelian; the isomorphisms preserve their group operations. The equivalence preserves the specified symmetries as well as all strong monoidal comparison maps. This gives the complete pair of invariants without assuming a trivial action or a vanishing cohomology class.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 20, Appendix A, Theorem 16: restrained Pic-category classification

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Theorem 16, PDF p. 20: both intrinsic abelian groups classify
restrained Pic-categories under symmetry-preserving equivalence.
No trivial-action or zero-cohomology hypothesis is imposed. -/
theorem restrainedPicClassification
    {C : Type u} {D : Type u1} [Category.{v} C] [Category.{v1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [SymmetricCategory C] [SymmetricCategory D]
    (hC : IsWeakTwoGroup C) (hD : IsWeakTwoGroup D)
    (rC : Restrained C) (rD : Restrained D) :
    letI := classGroup hC
    letI := classGroup hD
    Nonempty (PicEquivalence C D) ↔
      Nonempty (ObjectClasses C ≃* ObjectClasses D) ∧
      Nonempty (Aut (𝟙_ C) ≃* Aut (𝟙_ D)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
