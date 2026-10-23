-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_twoCopyConversions
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.twoCopyConversions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:22:48.499888+00:00
-- url     : https://prove2.me/theorems/eeaadda5-386a-47f7-8a9a-e1f316abdb6b
-- title:
--   Exact two-to-one tripartite conversions
-- statement:
--   For the common-bit law $P^3$ and even-parity law $P^x$ on three bits, finite local stochastic operations and public communication achieve
--   $$(P^3)^{\otimes2}\longrightarrow P^x,\qquad(P^x)^{\otimes2}\longrightarrow P^3.$$
--   The inputs are independent copies. Initially Eve has no side information; on every positive-probability public transcript the final law is the fixed target, hence secret from Eve.
--
--   Both directions consume two input copies and produce one output copy.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 8, §IV.C

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

/-- §IV.C, PDF p.8: two common-bit copies produce one xor law, and two xor
copies produce one common-bit law, exactly and independently of the transcript. -/
theorem twoCopyConversions :
    ExactSecretConversion (cCopies (exampleLaw 3) 2) (exampleLaw 4) ∧
    ExactSecretConversion (cCopies (exampleLaw 4) 2) (exampleLaw 3) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
