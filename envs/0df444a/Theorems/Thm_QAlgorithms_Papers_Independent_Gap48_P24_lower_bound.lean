-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_lower_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:28:21.60608+00:00
-- url     : https://prove2.me/theorems/1666feb9-4463-487e-a32b-0f4cb6f1752a
-- title:
--   Lower bound on the common-dilation Bures distance
-- statement:
--   Let $A$ be a unital complex C*-algebra, $H$ an arbitrary complete complex Hilbert space, and $T_1,T_2:A\to\mathcal B(H)$ bounded completely positive maps. No unitality, contractivity, normality or separability assumption is imposed on these maps or spaces. Write $\|T\|_{\rm cb}=\sup_{n\ge1}\|T\otimes\mathrm{id}_{M_n}\|$ for the completely bounded operator norm. Write $\beta$ for the infimum of $\|V_1-V_2\|$ over common nondegenerate *-representations $\pi:A\to\mathcal B(K)$ and bounded dilations satisfying $T_i(a)=V_i^*\pi(a)V_i$ for every $a$. Write $\beta_\pi$ for the corresponding infimum with $\pi$ fixed.
--
--   For all such maps, including $T_1=T_2=0$,
--   $$
--   \|T_1-T_2\|_{\rm cb}\le
--   \bigl(\sqrt{\|T_1\|_{\rm cb}}+\sqrt{\|T_2\|_{\rm cb}}\bigr)\beta(T_1,T_2).
--   $$
--   This gives the quantitative direction from close dilations to close completely positive maps.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 6, Proposition 3, (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 3, PDF pp.6–7, (13): lower bound, including the zero pair; C1. 
Source correction disclosure (PLAN identifiers C1, C6):
Printed: C1: Definition 1, PDF p.4, sets beta_pi=2 for an empty fiber and then takes beta=inf_pi beta_pi over all representations.
C6: The dilation formula on PDF p.2 calls pi a star homomorphism without explicitly requiring nondegeneracy.
Changed: C1: Keep the local default 2, but define the global dilation/scalar Bures distance as the infimum over actual common dilation pairs.
C6: Use nondegenerate representations in dilation/GNS fibers (unital on a unital domain). The embedding sigma in Theorem 2 and Proposition 9 remains arbitrary.
Why: C1: For A=C direct-sum C, H=C, T1(a,b)=9a, T2=0, pi(a,b)=b has an empty first fiber, forcing printed beta<=2 although Theorem 1 requires beta>=3. The proofs optimize only common fibers.
C6: The source repeatedly uses V*V=T(1) and norm(V)^2=norm(T(1)) on PDF pp.2-3 and 7. Degenerate pi with an invisible component of V invalidates these identities; nondegeneracy implements the proof convention without normalizing V or restricting CP maps.
-/
theorem lower_bound {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T1 T2 : A →L[ℂ] (H →L[ℂ] H)) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2) :
    cstarCompletelyBoundedNorm (T1 - T2) ≤ (Real.sqrt (cstarCompletelyBoundedNorm T1) + Real.sqrt (cstarCompletelyBoundedNorm T2)) *
      dilationBures H T1 T2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
