-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_upper_bound_attained
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.upper_bound_attained
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:30:59.760993+00:00
-- url     : https://prove2.me/theorems/1a89475d-3edf-4690-8d49-859fa00c8fcc
-- title:
--   Upper bound with attaining common dilations
-- statement:
--   Let $A$ be a unital complex C*-algebra, $H$ an arbitrary complete complex Hilbert space, and $T_1,T_2:A\to\mathcal B(H)$ bounded completely positive maps. No unitality, contractivity, normality or separability assumption is imposed on these maps or spaces. Write $\|T\|_{\rm cb}=\sup_{n\ge1}\|T\otimes\mathrm{id}_{M_n}\|$ for the completely bounded operator norm. Write $\beta$ for the infimum of $\|V_1-V_2\|$ over common nondegenerate *-representations $\pi:A\to\mathcal B(K)$ and bounded dilations satisfying $T_i(a)=V_i^*\pi(a)V_i$ for every $a$. Write $\beta_\pi$ for the corresponding infimum with $\pi$ fixed.
--
--   There exist a common representation $\pi$ and corresponding bounded dilations $V_1,V_2$ satisfying
--   $$
--   \|V_1-V_2\|=\beta_\pi(T_1,T_2)=\beta(T_1,T_2)
--   \le\sqrt{\|T_1-T_2\|_{\rm cb}}.
--   $$
--   The zero pair is included. This supplies both the upper continuity bound and actual attainment by dilations.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 9, Proposition 6, (25)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 6, PDF pp.9–11, (25): upper bound with actual dilation attainment;
the pair of zero maps is included; C1. 
Source correction disclosure (PLAN identifiers C1, C6):
Printed: C1: Definition 1, PDF p.4, sets beta_pi=2 for an empty fiber and then takes beta=inf_pi beta_pi over all representations.
C6: The dilation formula on PDF p.2 calls pi a star homomorphism without explicitly requiring nondegeneracy.
Changed: C1: Keep the local default 2, but define the global dilation/scalar Bures distance as the infimum over actual common dilation pairs.
C6: Use nondegenerate representations in dilation/GNS fibers (unital on a unital domain). The embedding sigma in Theorem 2 and Proposition 9 remains arbitrary.
Why: C1: For A=C direct-sum C, H=C, T1(a,b)=9a, T2=0, pi(a,b)=b has an empty first fiber, forcing printed beta<=2 although Theorem 1 requires beta>=3. The proofs optimize only common fibers.
C6: The source repeatedly uses V*V=T(1) and norm(V)^2=norm(T(1)) on PDF pp.2-3 and 7. Degenerate pi with an invisible component of V invalidates these identities; nondegeneracy implements the proof convention without normalizing V or restricting CP maps.
-/
theorem upper_bound_attained {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T1 T2 : A →L[ℂ] (H →L[ℂ] H)) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2) :
    ∃ R : RepresentationData A, ∃ V1 ∈ dilationFiber H T1 R,
    ∃ V2 ∈ dilationFiber H T2 R,
      ‖V1 - V2‖ = piDistance H T1 T2 R ∧
      piDistance H T1 T2 R = dilationBures H T1 T2 ∧
      dilationBures H T1 T2 ≤ Real.sqrt (cstarCompletelyBoundedNorm (T1 - T2)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
