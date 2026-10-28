-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_4
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:51:52.290223+00:00
-- url     : https://prove2.me/theorems/aae80bf1-c51a-4cfb-96b2-b765d1b6431b
-- title:
--   Root fidelity under partial trace
-- statement:
--   For nonnegative operators $\rho_{DE},\sigma_{DE}$ on nonzero finite-dimensional systems, write $\rho_D=\operatorname{tr}_E\rho_{DE}$ and $\sigma_D=\operatorname{tr}_E\sigma_{DE}$. Then
--
--   $$F(\rho_{DE},\sigma_{DE})\le F(\rho_D,\sigma_D).$$
--
--   Both arguments are traced and neither is required to be normalized.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 22, Lemma B.4

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

/-- Lemma B.4, Eq.162 (PDF p.22): both arguments undergo partial trace. -/
theorem lemmaB_4 {D E : Type*} [Fintype D] [Fintype E]
    [DecidableEq D] [DecidableEq E] [Nonempty D] [Nonempty E]
    (rho sigma : Op (D × E)) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) :
    rootFidelity rho sigma ≤ rootFidelity (traceRight rho) (traceRight sigma) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
