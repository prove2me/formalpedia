-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_tripartiteIncomparability
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.tripartiteIncomparability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:21:10.809188+00:00
-- url     : https://prove2.me/theorems/cda46882-5d86-4855-a5c9-e5a1d00aaca3
-- title:
--   Exact tripartite incomparability and block restrictions
-- statement:
--   Let $P^3$ and $P^x$ be the uniform common-bit and even-parity three-bit laws. Starting with no Eve information, local stochastic operations and public communication cannot convert one copy of either law into one secret copy of the other. More generally, for positive integers $k,l$,
--   $$(P^3)^{\otimes k}\longrightarrow(P^x)^{\otimes l}\ \Longrightarrow\ 2l\le k,\qquad(P^x)^{\otimes k}\longrightarrow(P^3)^{\otimes l}\ \Longrightarrow\ 2l\le k.$$
--   An exact secret conversion means that every positive-probability public transcript has the same indicated target law, independent of the transcript.
--
--   The prohibition concerns unit yield; two-to-one conversions remain possible.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 7, §IV.C, PDF pp.7–8

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

/-- §IV.C, PDF pp.7--8: one-copy incomparability and the sharp exact
finite-block restrictions in both directions. No zero-yield impossibility. -/
theorem tripartiteIncomparability :
    ¬ ExactSecretConversion (exampleLaw 3) (exampleLaw 4) ∧
    ¬ ExactSecretConversion (exampleLaw 4) (exampleLaw 3) ∧
    ∀ k l : ℕ, 0 < k → 0 < l →
      (ExactSecretConversion (cCopies (exampleLaw 3) k) (cCopies (exampleLaw 4) l) → 2*l ≤ k) ∧
      (ExactSecretConversion (cCopies (exampleLaw 4) k) (cCopies (exampleLaw 3) l) → 2*l ≤ k) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
