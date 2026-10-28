-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_pureStateValues
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.pureStateValues
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:24:56.519712+00:00
-- url     : https://prove2.me/theorems/84443ffb-dd7e-4f16-a281-2fd57dc3a95e
-- title:
--   Values on pure states, singlet and GHZ
-- statement:
--   Let $\rho=|\psi\rangle\langle\psi|$ for a unit vector on $n\ge2$ labelled finite local Hilbert spaces of nonzero dimensions, and let $\rho_i$ be its reduced density matrices. In bits,
--   $$S_n(\rho)=T_n(\rho)=\sum_i S(\rho_i).$$
--   For the normalized singlet $(|01\rangle-|10\rangle)/\sqrt2$, both values are $2$. For the plus GHZ state $(|000\rangle+|111\rangle)/\sqrt2$, both are $3$.
--
--   No factor $1/2$ is applied to either monotone.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 10, §V.B, (53); §V.E, (68)

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

/-- §V.B, PDF p.10, (53), repeated as (68), p.11: pure-state equality
and the explicit singlet=2 and plus-GHZ=3 examples, without half-normalization.
The corrupted ket in (68) is read using the intact equation (53). -/
theorem pureStateValues :
    (∀ (n : ℕ), 2 ≤ n → ∀ s : FiniteState n,
      QAlgorithms.Papers.Independent.Information100.P08.IsPure s.rho →
      qValue .dual s = localEntropySum s ∧ qValue .total s = localEntropySum s) ∧
    (∀ kind : InformationKind,
      info kind (pureDensity labelledSingletVector) (singleParties 2) ∅ = 2 ∧
      info kind (pureDensity (ghzVector 3)) (singleParties 3) ∅ = 3) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
