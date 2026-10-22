-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_continuity_stinespring
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.continuity_stinespring
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:26:50.47032+00:00
-- url     : https://prove2.me/theorems/9ab6d7b1-7303-426e-af04-35b57b83b45a
-- title:
--   Continuity of Stinespring dilation, with attainment and minimal direct sum
-- statement:
--   Let $A$ be a unital complex C*-algebra, $H$ an arbitrary complete complex Hilbert space, and $T_1,T_2:A\to\mathcal B(H)$ bounded completely positive maps. No unitality, contractivity, normality or separability assumption is imposed on these maps or spaces. Write $\|T\|_{\rm cb}=\sup_{n\ge1}\|T\otimes\mathrm{id}_{M_n}\|$ for the completely bounded operator norm. Write $\beta$ for the infimum of $\|V_1-V_2\|$ over common nondegenerate *-representations $\pi:A\to\mathcal B(K)$ and bounded dilations satisfying $T_i(a)=V_i^*\pi(a)V_i$ for every $a$. Write $\beta_\pi$ for the corresponding infimum with $\pi$ fixed.
--
--   Assume at least one of $T_1,T_2$ is nonzero. Then
--   $$
--   \frac{\|T_1-T_2\|_{\rm cb}}{\sqrt{\|T_1\|_{\rm cb}}+\sqrt{\|T_2\|_{\rm cb}}}
--   \le \beta(T_1,T_2)\le\sqrt{\|T_1-T_2\|_{\rm cb}}.
--   $$
--   There exist a common representation $\pi$ and dilations $V_1,V_2$ such that
--   $$
--   \|V_1-V_2\|=\beta_\pi(T_1,T_2)=\beta(T_1,T_2).
--   $$
--   For any chosen minimal dilations $(\widehat\pi_i,\widehat V_i,\widehat K_i)$, the common representation and attaining dilations can be taken on $\widehat\pi_1\oplus\widehat\pi_2$. Minimality means density of the linear span of $\widehat\pi_i(A)\widehat V_iH$.
--
--   This compares the stabilized distance of maps with the optimally aligned operator distance of their dilations.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 4, Theorem 1, (6)–(7), direct-sum refinement

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Theorem 1, PDF p.4, (6)–(7), including the direct-sum refinement.
C1: the printed all-representation infimum with empty-fiber value 2 is replaced
by the infimum over common representations, as used throughout the proof. 
Source correction disclosure (PLAN identifiers C1, C3, C6):
Printed: C1: Definition 1, PDF p.4, sets beta_pi=2 for an empty fiber and then takes beta=inf_pi beta_pi over all representations.
C3: The minimality sentence on PDF p.2 says the raw set {pi(a)V x} is dense.
C6: The dilation formula on PDF p.2 calls pi a star homomorphism without explicitly requiring nondegeneracy.
Changed: C1: Keep the local default 2, but define the global dilation/scalar Bures distance as the infimum over actual common dilation pairs.
C3: Use density of its complex linear span in IsMinimalStinespring.
C6: Use nondegenerate representations in dilation/GNS fibers (unital on a unital domain). The embedding sigma in Theorem 2 and Proposition 9 remains arbitrary.
Why: C1: For A=C direct-sum C, H=C, T1(a,b)=9a, T2=0, pi(a,b)=b has an empty first fiber, forcing printed beta<=2 although Theorem 1 requires beta>=3. The proofs optimize only common fibers.
C3: The proofs on PDF pp.8 and 14 explicitly use the closed linear span; this is the minimality condition used for their uniqueness and direct-sum arguments.
C6: The source repeatedly uses V*V=T(1) and norm(V)^2=norm(T(1)) on PDF pp.2-3 and 7. Degenerate pi with an invisible component of V invalidates these identities; nondegeneracy implements the proof convention without normalizing V or restricting CP maps.
-/
theorem continuity_stinespring {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T1 T2 : A →L[ℂ] (H →L[ℂ] H)) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2)
    (hne : T1 ≠ 0 ∨ T2 ≠ 0) :
    cstarCompletelyBoundedNorm (T1 - T2) / (Real.sqrt (cstarCompletelyBoundedNorm T1) + Real.sqrt (cstarCompletelyBoundedNorm T2)) ≤
      dilationBures H T1 T2 ∧
    dilationBures H T1 T2 ≤ Real.sqrt (cstarCompletelyBoundedNorm (T1 - T2)) ∧
    (∃ R : RepresentationData A, ∃ V1 ∈ dilationFiber H T1 R,
      ∃ V2 ∈ dilationFiber H T2 R,
        ‖V1 - V2‖ = piDistance H T1 T2 R ∧
        piDistance H T1 T2 R = dilationBures H T1 T2) ∧
    (∀ (R1 R2 : RepresentationData A) (V1 : H →L[ℂ] R1.K) (V2 : H →L[ℂ] R2.K),
      V1 ∈ dilationFiber H T1 R1 → V2 ∈ dilationFiber H T2 R2 →
      IsMinimalStinespring H R1 V1 → IsMinimalStinespring H R2 V2 →
      ∃ U1 ∈ dilationFiber H T1 (sumRepresentation R1 R2),
      ∃ U2 ∈ dilationFiber H T2 (sumRepresentation R1 R2),
        ‖U1 - U2‖ = piDistance H T1 T2 (sumRepresentation R1 R2) ∧
        piDistance H T1 T2 (sumRepresentation R1 R2) = dilationBures H T1 T2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
