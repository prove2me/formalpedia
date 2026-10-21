-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_pureToClassicalHalfSum
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.pureToClassicalHalfSum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:30:41.731975+00:00
-- url     : https://prove2.me/theorems/5de881f0-4a12-4915-817e-b91e56c6478d
-- title:
--   At least a factor-two decrease of the sum
-- statement:
--   Let $\rho$ be a normalized pure state on $n\ge2$ labelled local Hilbert spaces of nonzero finite dimensions. Suppose a finite adaptive local-instrument/public-communication protocol produces classical honest outputs $X$, with full public transcript $\tau$ heard by Eve. Then
--   $$\sum_\tau p(\tau)\bigl[S_n(P_{X\mid\tau})+T_n(P_{X\mid\tau})\bigr]\le\sum_iS(\rho_i)=\frac{S_n(\rho)+T_n(\rho)}2.$$
--   All entropies are in bits and zero-probability branches contribute zero.
--
--   The factor two compares the final sum with the initial sum; unconditional correlations created by public messages are not counted as secret.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 11, §V.E, (69),(73)

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

/-- §V.E, PDF pp.11--12, (69),(73): initial pure to final classical
extraction decreases the SUM by at least two, on average conditional on the
entire public transcript. There is no bound on unconditional public correlation. -/
theorem pureToClassicalHalfSum {n : ℕ} (hn : 2 ≤ n) (s : FiniteState n)
    (hpure : QAlgorithms.Papers.Independent.Information100.P08.IsPure s.rho)
    (out : List (ℝ × FiniteState n)) (hprotocol : QLOPC s out)
    (hclassical : ∀ z ∈ out, 0 < z.1 → IsDiagonalOutput z.2) :
    (out.map fun z => z.1 * (cValue .dual (readout z.2) +
      cValue .total (readout z.2))).sum ≤ localEntropySum s ∧
    localEntropySum s = (qValue .dual s + qValue .total s) / 2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
