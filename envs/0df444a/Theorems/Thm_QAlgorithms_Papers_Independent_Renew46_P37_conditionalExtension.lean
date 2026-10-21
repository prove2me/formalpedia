-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_conditionalExtension
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.conditionalExtension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:11:50.751247+00:00
-- url     : https://prove2.me/theorems/f8c8a209-a229-4f7c-b596-eceb4d426def
-- title:
--   Conditional extension to Eve
-- statement:
--   Let $n\ge2$ and let $M$ satisfy nonnegativity, product vanishing, average local/public monotonicity, independent-product additivity, and continuity on each fixed finite alphabet. For a normalized finite joint law of honest variables $A=(A_1,\ldots,A_n)$ and Eve's variable $E$, define
--   $$M_1(P_{AE})=\sum_{e:p(e)>0}p(e)M(P_{A\mid e}).$$
--   This extension is nonnegative, vanishes on conditionally product laws, is additive on independent honest/Eve products, and is continuous on each fixed honest/Eve alphabet. Honest local stochastic operations or public messages decrease it on average; Eve's public disclosure increases it on average. These statements condition on the entire public history.
--
--   Eve-local monotonicity can fail: if $A,B$ are independent fair bits and $E=A\oplus B$, then the conditional mutual information is $1$ bit, and becomes $0$ when Eve forgets $E$. This is a possible failure, not a failure for every $M$.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 4, §II.B.2

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

/-- §II.B.2, PDF p.4: conditional averaging inherits the stated basic
properties, honest local/public monotonicity, and Eve-public monotonicity.
The explicit xor/Eve example witnesses the possible failure of property 7;
no universal failure for every M is asserted. -/
theorem conditionalExtension {n : ℕ} (hn : 2 ≤ n) (M : CData n → ℝ)
    (hM : IsCMonotone M) :
    ExtensionBasics (conditionalAverage M) ∧ ExtensionMonotonicity (conditionalAverage M) ∧
    EValid conditionalCounterexample ∧
    conditionalAverage (cValue .dual : CData 2 → ℝ)
      (processE conditionalCounterexample (fun (_ : Fin 2) (_ : Fin 1) => 1)) = 0 ∧
    conditionalAverage (cValue .dual : CData 2 → ℝ) conditionalCounterexample = 1 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
