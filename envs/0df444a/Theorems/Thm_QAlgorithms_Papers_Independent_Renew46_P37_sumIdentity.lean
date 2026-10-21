-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_sumIdentity
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.sumIdentity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:16:48.621252+00:00
-- url     : https://prove2.me/theorems/e640fe15-8aaf-4afd-abae-852fde470a2e
-- title:
--   The sum of the two monotones
-- statement:
--   For a normalized finite $n$-party law on nonempty alphabets, $n\ge2$, let $A_{-i}$ contain all parties except $i$. In bits,
--   $$S_n(P)+T_n(P)=\sum_{i=1}^{n}I(A_i:A_{-i}).$$
--   For two parties this is $2I(A_1:A_2)$.
--
--   The identity is unnormalized and provides the linear relation among the five tripartite monotones.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 5, §III.C, (22)

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

/-- §III.C, PDF p.5, (22): the unnormalized sum, including 2I at n=2. -/
theorem sumIdentity {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    cValue .dual p + cValue .total p =
      ∑ i, lawCMI p {i} (Finset.univ.erase i) ∅ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
