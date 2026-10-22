-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_continuity_general_range
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.continuity_general_range
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:27:39.318004+00:00
-- url     : https://prove2.me/theorems/dc58cf23-2f0b-4ba2-bfc2-1bb9c969d3d0
-- title:
--   Continuity for general range algebras
-- statement:
--   Let $A,B$ be unital complex C*-algebras and $T_1,T_2:A\to B$ bounded completely positive maps, with no normalization or normality condition. The intrinsic distance $\beta_{\rm int}(T_1,T_2)$ is the infimum of $\|\widehat T_{11}(1_A)+\widehat T_{22}(1_A)-\widehat T_{12}(1_A)-\widehat T_{21}(1_A)\|^{1/2}$ over completely positive maps $\widehat T:A\to M_2(B)$ with diagonal entries $T_1,T_2$. All matrix algebras carry their C*-operator norms; $\|\cdot\|_{\rm cb}$ denotes the supremum of all finite amplification norms.
--
--   The lower bound, including the zero pair, is
--   $$
--   \|T_1-T_2\|_{\rm cb}\le
--   \bigl(\sqrt{\|T_1\|_{\rm cb}}+\sqrt{\|T_2\|_{\rm cb}}\bigr)\beta_{\rm int}(T_1,T_2).
--   $$
--   If $B$ is injective, also
--   $$
--   \beta_{\rm int}(T_1,T_2)\le\sqrt{\|T_1-T_2\|_{\rm cb}},\qquad
--   \beta_{\rm int}(T_1,T_2)=\beta(\sigma\circ T_1,\sigma\circ T_2)
--   $$
--   for every faithful *-representation $\sigma:B\to\mathcal B(H)$ on an arbitrary complete complex Hilbert space. On the right, $\beta$ is the common-dilation infimum. Injectivity is expressed by the equivalent existence of a contractive CP retraction for every faithful concrete realization of $B$.
--
--   This distinguishes the unconditional lower bound from the injective-range upper bound and embedding invariance.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 6, Theorem 2, (11)–(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Theorem 2, PDF pp.6,13–14: multiplicative form includes the zero pair.
The upper bound and faithful-embedding equality require injective B. 
Source correction disclosure (PLAN identifiers C1, C4, C6):
Printed: C1: Definition 1, PDF p.4, sets beta_pi=2 for an empty fiber and then takes beta=inf_pi beta_pi over all representations.
C4: Theorem 2, PDF p.6, displays a quotient by sqrt(norm_cb T1)+sqrt(norm_cb T2) without excluding the zero pair.
C6: The dilation formula on PDF p.2 calls pi a star homomorphism without explicitly requiring nondegeneracy.
Changed: C1: Keep the local default 2, but define the global dilation/scalar Bures distance as the infimum over actual common dilation pairs.
C4: State the multiplicative lower bound, retaining both zero maps; keep the source nonzero-pair quotient in Theorem 1.
C6: Use nondegenerate representations in dilation/GNS fibers (unital on a unital domain). The embedding sigma in Theorem 2 and Proposition 9 remains arbitrary.
Why: C1: For A=C direct-sum C, H=C, T1(a,b)=9a, T2=0, pi(a,b)=b has an empty first fiber, forcing printed beta<=2 although Theorem 1 requires beta>=3. The proofs optimize only common fibers.
C4: The printed quotient is undefined at T1=T2=0. The multiplicative form is equivalent for every nonzero pair and reads 0<=0 at the zero pair, as in Proposition 3.
C6: The source repeatedly uses V*V=T(1) and norm(V)^2=norm(T(1)) on PDF pp.2-3 and 7. Degenerate pi with an invisible component of V invalidates these identities; nondegeneracy implements the proof convention without normalizing V or restricting CP maps.
-/
theorem continuity_general_range {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (T1 T2 : A →L[ℂ] B) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2) :
    cstarCompletelyBoundedNorm (T1 - T2) ≤ (Real.sqrt (cstarCompletelyBoundedNorm T1) + Real.sqrt (cstarCompletelyBoundedNorm T2)) *
      intrinsicBures T1 T2 ∧
    (IsInjective B → intrinsicBures T1 T2 ≤ Real.sqrt (cstarCompletelyBoundedNorm (T1 - T2)) ∧
      ∀ (H : CompleteComplexHilbert.{u}) (sigma : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)), Function.Injective sigma →
        intrinsicBures T1 T2 = dilationBures H (sigma ∘ T1) (sigma ∘ T2)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
