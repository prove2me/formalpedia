-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_pairDistillation
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.pairDistillation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:22:01.251998+00:00
-- url     : https://prove2.me/theorems/6e21a667-4daf-4b40-9fd4-8b7195a78de9
-- title:
--   One secret pair from either tripartite law
-- statement:
--   Let $P^3$ be uniform on $000,111$ and $P^x$ uniform on $000,110,101,011$. Let $P_{AB}$ be a uniform shared bit for $A,B$ with $C$ constant. With initially independent Eve and public messages all heard by Eve, exact local stochastic/public-communication conversions exist:
--   $$P^x\longrightarrow P_{AB},\qquad P^3\longrightarrow P_{AB}.$$
--   For every positive-probability public transcript, the final $AB$ bit is uniform and independent of that transcript and the final $C$ register.
--
--   This is a secret pair output, rather than a bit still shared with the spectator.
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

/-- §IV.C, PDF p.8: a secret pair AB from either tripartite law. The target
has a constant C register; on each public transcript AB is uniform and secret.
For xor, the announced C bit is followed by the transcript-dependent flip. -/
theorem pairDistillation :
    ExactSecretConversion (exampleLaw 4) (exampleLaw 0) ∧ ExactSecretConversion (exampleLaw 3) (exampleLaw 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
