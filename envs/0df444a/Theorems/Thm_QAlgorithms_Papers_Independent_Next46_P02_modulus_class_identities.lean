-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_modulus_class_identities
-- name    : QAlgorithms.Papers.Independent.Next46.P02.modulus_class_identities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:27:19.231983+00:00
-- url     : https://prove2.me/theorems/bb95b8e1-d188-4dab-bcc3-b1af211f2cea
-- title:
--   Modulus identities for trace and Hilbert–Schmidt classes
-- statement:
--   Let $T$ be a bounded endomorphism of a complete real or complex Hilbert space $H$. Put $|T|=(T^*T)^{1/2}$ and let $\mathcal B_1(H),\mathcal B_2(H)$ be the independently defined trace and Hilbert–Schmidt classes. Then
--
--   $$
--   T\in\mathcal B_1(H)\iff |T|\in\mathcal B_1(H)\iff |T|^{1/2}\in\mathcal B_2(H),
--   $$
--   $$
--   T\in\mathcal B_2(H)\iff |T|\in\mathcal B_2(H)\iff |T|^2\in\mathcal B_1(H).
--   $$
--
--   On the respective finite-norm domains,
--
--   $$
--   \|T\|_1=\||T|\|_1=\||T|^{1/2}\|_2^2,\qquad
--   \|T\|_2^2=\||T|\|_2^2=\||T|^2\|_1.
--   $$
--
--   The squared modulus is $T^*T$, which fixes the parentheses essential to these identities.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 9, §5 opening, unnumbered modulus/class identities

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF pp.9–10: both modulus/class chains and both norm chains.
All real norm equalities have finite-domain membership guards. -/
theorem modulus_class_identities (T : H →L[F] H) :
    (IsModulusTraceClass T ↔ IsModulusTraceClass (hilbertOperatorModulus T)) ∧
    (IsModulusTraceClass (hilbertOperatorModulus T) ↔ IsHilbertSchmidt (hilbertPositiveSqrt (hilbertOperatorModulus T))) ∧
    (IsModulusTraceClass T → modulusTraceNorm T = modulusTraceNorm (hilbertOperatorModulus T) ∧
      modulusTraceNorm (hilbertOperatorModulus T) = hilbertSchmidtNorm (hilbertPositiveSqrt (hilbertOperatorModulus T)) ^ 2) ∧
    (IsHilbertSchmidt T ↔ IsHilbertSchmidt (hilbertOperatorModulus T)) ∧
    (IsHilbertSchmidt (hilbertOperatorModulus T) ↔
      IsModulusTraceClass ((hilbertOperatorModulus T).comp (hilbertOperatorModulus T))) ∧
    (IsHilbertSchmidt T → hilbertSchmidtNorm T ^ 2 = hilbertSchmidtNorm (hilbertOperatorModulus T) ^ 2 ∧
      hilbertSchmidtNorm (hilbertOperatorModulus T) ^ 2 =
        modulusTraceNorm ((hilbertOperatorModulus T).comp (hilbertOperatorModulus T))) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
