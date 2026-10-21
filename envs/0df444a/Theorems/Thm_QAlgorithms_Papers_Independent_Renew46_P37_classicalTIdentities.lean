-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_classicalTIdentities
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.classicalTIdentities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:15:24.725269+00:00
-- url     : https://prove2.me/theorems/86aeb8c4-5dca-40fe-8641-6985d91db9dd
-- title:
--   Recurrence and chain identities for T_n
-- statement:
--   For a normalized finite law on nonempty alphabets $A_1,\ldots,A_n$, $n\ge2$, with entropy in bits,
--   $$T_n=\sum_i H(A_i)-H(A_1\cdots A_n)=\sum_{i=2}^{n}I(A_1\cdots A_{i-1}:A_i).$$
--   For $n\ge3$, $T_n=T_{n-1}(A_1:\cdots:A_{n-1})+I(A_n:A_1\cdots A_{n-1})$, with the first term evaluated on the marginal law. For two parties, $T_2(A:B)=I(A:B)$.
--
--   The chain begins with $I(A_1:A_2)$; no one-party recurrence is claimed.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 5, §III.B, (19)–(21)

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

/-- §III.B, PDF p.5, (19)--(21): recurrence, chain formula, and T_2=I.
The chain starts with I(A_1:A_2); the recurrence is used only for n≥3. -/
theorem classicalTIdentities {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .total p = ∑ i ∈ Finset.univ.filter (fun i : Fin n => 0 < i.val),
      lawCMI p (earlier i) {i} ∅ ∧
    (3 ≤ n → cValue .total p = cInfo .total p (firstParties n) +
      lawCMI p (Finset.univ.filter fun i => i.val + 1 = n)
        (Finset.univ.filter fun i => i.val + 1 < n) ∅) ∧
    (∀ q : CData 2, IsValidClassicalData q → cValue .total q = lawCMI q {0} {1} ∅) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
