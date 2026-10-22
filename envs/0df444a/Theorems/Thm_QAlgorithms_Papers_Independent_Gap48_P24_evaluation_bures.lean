-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_evaluation_bures
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.evaluation_bures
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:30:00.422069+00:00
-- url     : https://prove2.me/theorems/d68a7a26-f33e-4185-94e9-f3ec9ecc50a2
-- title:
--   Evaluation of the Bures distance via contraction intertwiners
-- statement:
--   Let $A$ be a unital complex C*-algebra, $H$ an arbitrary complete complex Hilbert space, and $T_1,T_2:A\to\mathcal B(H)$ bounded completely positive maps. No unitality, contractivity, normality or separability assumption is imposed on these maps or spaces. Write $\|T\|_{\rm cb}=\sup_{n\ge1}\|T\otimes\mathrm{id}_{M_n}\|$ for the completely bounded operator norm. Write $\beta$ for the infimum of $\|V_1-V_2\|$ over common nondegenerate *-representations $\pi:A\to\mathcal B(K)$ and bounded dilations satisfying $T_i(a)=V_i^*\pi(a)V_i$ for every $a$. Write $\beta_\pi$ for the corresponding infimum with $\pi$ fixed.
--
--   Choose any dilations $(\pi_i,V_i,K_i)$ of $T_i$, and define
--   $$
--   \mathcal M=\{V_1^*WV_2:\ W:K_2\to K_1\text{ bounded},\ \|W\|\le1,
--   \ W\pi_2(a)=\pi_1(a)W\ \text{for every }a\in A\}.
--   $$
--   The following hold.
--
--   1. $\mathcal M$ equals the set obtained from any other pair of dilations of the same maps.
--   2. With $\mathcal N_\pi=\{U_1^*U_2:U_i\in S(T_i,\pi)\}$,
--   $$\mathcal M=\bigcup_{\pi\text{ common}}\mathcal N_\pi.$$
--   3. Some common representation satisfies $\beta=\beta_\pi$. For any chosen minimal dilations of the two maps one may take $\pi=\widehat\pi_1\oplus\widehat\pi_2$.
--
--   This gives a dilation-independent overlap set and an explicit representation on which the representation infimum is achieved.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 8, Lemma 5, clauses (1)–(3), (18)–(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma 5, PDF pp.8–9, all three clauses: independence of dilations, union of
common overlaps, and attained representation infimum with minimal direct sum; C1. 
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
theorem evaluation_bures {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T1 T2 : A →L[ℂ] (H →L[ℂ] H)) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2)
    (R1 R2 : RepresentationData A) (V1 : H →L[ℂ] R1.K) (V2 : H →L[ℂ] R2.K)
    (hd1 : V1 ∈ dilationFiber H T1 R1) (hd2 : V2 ∈ dilationFiber H T2 R2) :
    (∀ (S1 S2 : RepresentationData A) (U1 : H →L[ℂ] S1.K) (U2 : H →L[ℂ] S2.K),
      U1 ∈ dilationFiber H T1 S1 → U2 ∈ dilationFiber H T2 S2 →
      intertwinerSet H R1 R2 V1 V2 = intertwinerSet H S1 S2 U1 U2) ∧
    intertwinerSet H R1 R2 V1 V2 = commonOverlaps H T1 T2 ∧
    (∃ R : RepresentationData A,
      (dilationFiber H T1 R).Nonempty ∧ (dilationFiber H T2 R).Nonempty ∧
      dilationBures H T1 T2 = piDistance H T1 T2 R) ∧
    (∀ (S1 S2 : RepresentationData A) (U1 : H →L[ℂ] S1.K) (U2 : H →L[ℂ] S2.K),
      U1 ∈ dilationFiber H T1 S1 → U2 ∈ dilationFiber H T2 S2 →
      IsMinimalStinespring H S1 U1 → IsMinimalStinespring H S2 U2 →
      (dilationFiber H T1 (sumRepresentation S1 S2)).Nonempty ∧
      (dilationFiber H T2 (sumRepresentation S1 S2)).Nonempty ∧
      dilationBures H T1 T2 = piDistance H T1 T2 (sumRepresentation S1 S2)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
