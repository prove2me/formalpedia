-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_bures_definitions_consistent
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.bures_definitions_consistent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:31:35.902379+00:00
-- url     : https://prove2.me/theorems/1af72b12-981d-4276-87f7-0df09a1c630b
-- title:
--   Consistency of dilation and intrinsic Bures distances
-- statement:
--   Let $A$ be a unital complex C*-algebra, $H$ an arbitrary complete complex Hilbert space, and $T_1,T_2:A\to\mathcal B(H)$ bounded completely positive maps. No unitality, contractivity, normality or separability assumption is imposed on these maps or spaces. Write $\|T\|_{\rm cb}=\sup_{n\ge1}\|T\otimes\mathrm{id}_{M_n}\|$ for the completely bounded operator norm. Write $\beta$ for the infimum of $\|V_1-V_2\|$ over common nondegenerate *-representations $\pi:A\to\mathcal B(K)$ and bounded dilations satisfying $T_i(a)=V_i^*\pi(a)V_i$ for every $a$. Write $\beta_\pi$ for the corresponding infimum with $\pi$ fixed.
--
--   Let $\beta_{\rm int}$ instead be defined by the infimum of the square root of
--   $\|\widehat T_{11}(1_A)+\widehat T_{22}(1_A)-\widehat T_{12}(1_A)-\widehat T_{21}(1_A)\|$
--   over CP extensions $\widehat T:A\to M_2(\mathcal B(H))$ with diagonal entries $T_i$. Then
--   $$\beta(T_1,T_2)=\beta_{\rm int}(T_1,T_2).$$
--   This identifies two independently constructed distances, including for zero maps.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 11, Proposition 7, (30)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 7, PDF pp.11–12, (30): equality of two separately defined distances;
C1 corrects only the dilation definition. 
Source correction disclosure (PLAN identifiers C1, C6):
Printed: C1: Definition 1, PDF p.4, sets beta_pi=2 for an empty fiber and then takes beta=inf_pi beta_pi over all representations.
C6: The dilation formula on PDF p.2 calls pi a star homomorphism without explicitly requiring nondegeneracy.
Changed: C1: Keep the local default 2, but define the global dilation/scalar Bures distance as the infimum over actual common dilation pairs.
C6: Use nondegenerate representations in dilation/GNS fibers (unital on a unital domain). The embedding sigma in Theorem 2 and Proposition 9 remains arbitrary.
Why: C1: For A=C direct-sum C, H=C, T1(a,b)=9a, T2=0, pi(a,b)=b has an empty first fiber, forcing printed beta<=2 although Theorem 1 requires beta>=3. The proofs optimize only common fibers.
C6: The source repeatedly uses V*V=T(1) and norm(V)^2=norm(T(1)) on PDF pp.2-3 and 7. Degenerate pi with an invisible component of V invalidates these identities; nondegeneracy implements the proof convention without normalizing V or restricting CP maps.
-/
theorem bures_definitions_consistent {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T1 T2 : A →L[ℂ] (H →L[ℂ] H)) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2) :
    dilationBures H T1 T2 = intrinsicBures T1 T2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
