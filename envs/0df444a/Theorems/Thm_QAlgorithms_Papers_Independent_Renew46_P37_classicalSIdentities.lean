-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_classicalSIdentities
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.classicalSIdentities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:14:25.089707+00:00
-- url     : https://prove2.me/theorems/e4254bc3-6367-4fe1-ad54-2dce9d094de8
-- title:
--   Entropy and chain identities for S_n
-- statement:
--   Let $A_1,\ldots,A_n$, $n\ge2$, have a normalized finite joint law on nonempty alphabets, and use entropy in bits. Write $A_{<i}=(A_1,\ldots,A_{i-1})$, $A_{>i}=(A_{i+1},\ldots,A_n)$, and $A_{-i}$ for all variables except $A_i$. Then
--   $$S_n=H(A)-\sum_i H(A_i\mid A_{-i})=\sum_iH(A_{-i})-(n-1)H(A)=\sum_{i=1}^{n-1}I(A_i:A_{>i}\mid A_{<i}).$$
--   For $n\ge3$, grouping the final two parties gives $S_n=S_{n-1}(A_1:\cdots:A_{n-1}A_n)+I(A_{n-1}:A_n\mid A_1\cdots A_{n-2})$. The base case is $S_2(A:B)=I(A:B)$.
--
--   These are the entropy, chain, and recurrence descriptions of the same functional.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 4, §III.A, (12)–(16)

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

/-- §III.A, PDF pp.4--5, (12)--(16): entropy, conditional-information chain,
last-pair recurrence, and the explicit two-party base case. -/
theorem classicalSIdentities {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .dual p = cH p Finset.univ -
      ∑ i, (cH p Finset.univ - cH p (Finset.univ.erase i)) ∧
    cValue .dual p = (∑ i, cH p (Finset.univ.erase i)) -
      (n-1 : ℕ) * cH p Finset.univ ∧
    cValue .dual p = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n),
      lawCMI p {i} (later i) (earlier i) ∧
    (3 ≤ n → cValue .dual p = cInfo .dual p (mergeLast n) +
      lawCMI p (Finset.univ.filter fun i => i.val + 2 = n)
        (Finset.univ.filter fun i => i.val + 1 = n)
        (Finset.univ.filter fun i => i.val + 2 < n)) ∧
    (∀ q : CData 2, IsValidClassicalData q → cValue .dual q = lawCMI q {0} {1} ∅) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
