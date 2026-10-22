-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_embedding_bures
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.embedding_bures
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:33:31.76645+00:00
-- url     : https://prove2.me/theorems/2552eb5d-49bd-4935-9ecf-45ba7816fb35
-- title:
--   Representations and injective range algebras
-- statement:
--   Let $A,B$ be unital complex C*-algebras and $T_1,T_2:A\to B$ bounded completely positive maps, with no normalization or normality condition. The intrinsic distance $\beta_{\rm int}(T_1,T_2)$ is the infimum of $\|\widehat T_{11}(1_A)+\widehat T_{22}(1_A)-\widehat T_{12}(1_A)-\widehat T_{21}(1_A)\|^{1/2}$ over completely positive maps $\widehat T:A\to M_2(B)$ with diagonal entries $T_1,T_2$. All matrix algebras carry their C*-operator norms; $\|\cdot\|_{\rm cb}$ denotes the supremum of all finite amplification norms.
--
--   For every *-representation $\sigma:B\to\mathcal B(H)$, where $H$ is an arbitrary complete complex Hilbert space,
--   $$\beta(\sigma\circ T_1,\sigma\circ T_2)\le\beta_{\rm int}(T_1,T_2).$$
--   The left distance is the common-dilation Bures distance. If $B$ is injective and $\sigma$ is faithful, then
--   $$\beta_{\rm int}(T_1,T_2)=\beta(\sigma\circ T_1,\sigma\circ T_2).$$
--   The unconditional inequality permits zero and degenerate representations. This controls the effect of a concrete embedding and gives invariance for faithful embeddings of injective ranges.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 13, Proposition 9, (36)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 9, PDF p.13, (36): every representation, including degenerate and
zero representations; equality additionally requires injectivity and faithfulness. 
Source correction disclosure (PLAN identifiers C1, C6):
Printed: C1: Definition 1, PDF p.4, sets beta_pi=2 for an empty fiber and then takes beta=inf_pi beta_pi over all representations.
C6: The dilation formula on PDF p.2 calls pi a star homomorphism without explicitly requiring nondegeneracy.
Changed: C1: Keep the local default 2, but define the global dilation/scalar Bures distance as the infimum over actual common dilation pairs.
C6: Use nondegenerate representations in dilation/GNS fibers (unital on a unital domain). The embedding sigma in Theorem 2 and Proposition 9 remains arbitrary.
Why: C1: For A=C direct-sum C, H=C, T1(a,b)=9a, T2=0, pi(a,b)=b has an empty first fiber, forcing printed beta<=2 although Theorem 1 requires beta>=3. The proofs optimize only common fibers.
C6: The source repeatedly uses V*V=T(1) and norm(V)^2=norm(T(1)) on PDF pp.2-3 and 7. Degenerate pi with an invisible component of V invalidates these identities; nondegeneracy implements the proof convention without normalizing V or restricting CP maps.
-/
theorem embedding_bures {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (T1 T2 : A →L[ℂ] B) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2)
    (H : CompleteComplexHilbert.{u}) (sigma : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    dilationBures H (sigma ∘ T1) (sigma ∘ T2) ≤ intrinsicBures T1 T2 ∧
    (IsInjective B → Function.Injective sigma →
      intrinsicBures T1 T2 = dilationBures H (sigma ∘ T1) (sigma ∘ T2)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
