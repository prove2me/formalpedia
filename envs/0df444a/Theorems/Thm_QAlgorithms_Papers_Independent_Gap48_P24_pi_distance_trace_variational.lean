-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P24_pi_distance_trace_variational
-- name    : QAlgorithms.Papers.Independent.Gap48.P24.pi_distance_trace_variational
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:29:08.306806+00:00
-- url     : https://prove2.me/theorems/a2c76a79-78e7-4c97-aff3-ae088c110c5d
-- title:
--   Trace-class evaluation of a common representation distance
-- statement:
--   Let $A$ be a unital complex C*-algebra, $H$ an arbitrary complete complex Hilbert space, and $T_1,T_2:A\to\mathcal B(H)$ bounded completely positive maps. No unitality, contractivity, normality or separability assumption is imposed on these maps or spaces. Write $\|T\|_{\rm cb}=\sup_{n\ge1}\|T\otimes\mathrm{id}_{M_n}\|$ for the completely bounded operator norm. Write $\beta$ for the infimum of $\|V_1-V_2\|$ over common nondegenerate *-representations $\pi:A\to\mathcal B(K)$ and bounded dilations satisfying $T_i(a)=V_i^*\pi(a)V_i$ for every $a$. Write $\beta_\pi$ for the corresponding infimum with $\pi$ fixed.
--
--   Fix a representation $\pi$ whose two dilation fibers are nonempty, and put $\mathcal N_\pi=\{V_1^*V_2:V_i\in S(T_i,\pi)\}$. If $H\ne\{0\}$, let $\mathcal D(H)$ be the positive trace-class operators of trace one. Then
--   $$
--   \beta_\pi(T_1,T_2)^2=
--   \inf_{N\in\mathcal N_\pi}\sup_{\rho\in\mathcal D(H)}
--   \bigl[\operatorname{tr}(\rho T_1(1_A))+\operatorname{tr}(\rho T_2(1_A))
--   -2\operatorname{Re}\operatorname{tr}(\rho N)\bigr].
--   $$
--   For $H=\{0\}$ the variational expression is explicitly assigned zero, and the same identity holds. The trace may be evaluated in any complete orthonormal basis; no countability of that basis is required.
--
--   This expresses the dilation distance through trace-class tests and overlaps rather than individual dilation differences.
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, PDF p. 7, Lemma 4, (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Lemma 4, PDF p.7, (16). C2: printed arbitrary pi is changed to a common
representation, because the proof chooses vectors in both fibers. For H=0 the
unit-trace state set is empty and the variational value is explicitly zero. 
Source correction disclosure (PLAN identifiers C2, C6):
Printed: C2: Lemma 4, PDF p.7, allows an arbitrary representation pi and writes a supremum over unit-trace positive operators, without a zero-H convention.
C6: The dilation formula on PDF p.2 calls pi a star homomorphism without explicitly requiring nondegeneracy.
Changed: C2: Require both dilation fibers nonempty; for the zero Hilbert space assign the trace variational quantity the explicit value zero.
C6: Use nondegenerate representations in dilation/GNS fibers (unital on a unital domain). The embedding sigma in Theorem 2 and Proposition 9 remains arbitrary.
Why: C2: An empty fiber gives beta_pi squared=4 but an empty overlap infimum; the proof chooses Vi in both fibers. At H=0 there are no trace-one states, while the dilation distance is zero.
C6: The source repeatedly uses V*V=T(1) and norm(V)^2=norm(T(1)) on PDF pp.2-3 and 7. Degenerate pi with an invisible component of V invalidates these identities; nondegeneracy implements the proof convention without normalizing V or restricting CP maps.
-/
theorem pi_distance_trace_variational {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : CompleteComplexHilbert.{u}) {I : Type u} (b : HilbertBasis I ℂ H)
    (T1 T2 : A →L[ℂ] (H →L[ℂ] H)) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2)
    (R : RepresentationData A)
    (hc : (dilationFiber H T1 R).Nonempty ∧ (dilationFiber H T2 R).Nonempty) :
    piDistance H T1 T2 R ^ 2 = traceVariational H b T1 T2 R := by sorry

end QAlgorithms.Papers.Independent.Gap48.P24

end
