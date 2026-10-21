-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_9
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:54:23.36499+00:00
-- url     : https://prove2.me/theorems/5e74d6a6-6c2c-4774-89b6-4a977683df96
-- title:
--   Continuity of root fidelity
-- statement:
--   For nonnegative operators $\rho,\rho',\sigma$ on the same nonzero finite-dimensional system,
--
--   $$\bigl(F(\rho,\sigma)-F(\rho',\sigma)\bigr)^2\le\|\rho-\rho'\|_1\operatorname{tr}\sigma.$$
--
--   All three operators may be unnormalized, and the square applies to the full real fidelity difference.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 23, Lemma B.9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma B.9, Eq.173 (PDF p.23): square of the full fidelity difference. -/
theorem lemmaB_9 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho rhoPrime sigma : Op I) (hrho : rho.PosSemidef)
    (hprime : rhoPrime.PosSemidef) (hsigma : sigma.PosSemidef) :
    (rootFidelity rho sigma - rootFidelity rhoPrime sigma) ^ 2 ≤
      traceNorm (rho-rhoPrime) * sigma.trace.re := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
