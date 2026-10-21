-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_classicalMonotones
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.classicalMonotones
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:10:52.860903+00:00
-- url     : https://prove2.me/theorems/f82b4905-5823-40d9-afe3-ab6e7ef2d4e9
-- title:
--   The two classical multipartite secrecy monotones
-- statement:
--   For $n\ge2$, let $P$ be a normalized law on arbitrary nonempty finite local alphabets $A_1,\ldots,A_n$. Entropies are in bits, with $0\log0=0$. Put $A_{-i}=(A_j)_{j\ne i}$ and $A=(A_1,\ldots,A_n)$. Define
--   $$S_n(P)=\sum_i H(A_{-i})-(n-1)H(A),\qquad T_n(P)=\sum_i H(A_i)-H(A).$$
--   Both functions are nonnegative, vanish on product laws, are additive on independent partywise products, are continuous on each fixed alphabet, and are symmetric in the parties. Local stochastic operations and public communication cannot increase their expected values, conditioned on the communicated outcome. Initially Eve has no information, and every public outcome is known to Eve. For two parties, $S_2=T_2=I(A_1:A_2)$.
--
--   These are the two unnormalized classical secrecy measures; Eve-dependent extensions are separate results.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 1, Abstract; §III, (12)–(17),(24),(28),(30),(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P37

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

/-- Abstract, PDF p.1; §§III.A--E, PDF pp.4--7, (12),(17),(24),(28),(30),(35).
Both unnormalized quantities obey properties 1--6, are symmetric, and reduce
to mutual information for two parties. No property of Eve is asserted here. -/
theorem classicalMonotones :
    (∀ n : ℕ, 2 ≤ n → ∀ kind : InformationKind,
      IsCMonotone (cValue kind : CData n → ℝ)) ∧
    (∀ (n : ℕ) (p : CData n), 2 ≤ n → IsValidClassicalData p →
      ∀ (e : Equiv.Perm (Fin n)) (kind : InformationKind),
        cValue kind (permuteData p e) = cValue kind p) ∧
    (∀ p : CData 2, IsValidClassicalData p →
      cValue .dual p = lawCMI p {0} {1} ∅ ∧
      cValue .total p = lawCMI p {0} {1} ∅) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
