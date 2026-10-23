-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_eprSourceRegions
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.eprSourceRegions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:48:37.659529+00:00
-- url     : https://prove2.me/theorems/625a4383-b639-43a2-8faa-0559aabd95ad
-- title:
--   Example IV.8: Uniform {PhiPlus,PhiMinus} EPR source: Rq,Fe⊆Rq,Fbar⊆{R1,R2≥1/2}.
-- statement:
--   Consider the source uniformly distributed on the two Bell states $|\Phi^+\rangle,|\Phi^-\rangle$, with each party holding one qubit. Its average is $(|00\rangle\langle00|+|11\rangle\langle11|)/2$. The following are necessary rate constraints, not an exact quadrant characterization.
--
--   $$
--   \mathcal R_{q,F_e}\subseteq\mathcal R_{q,\bar F}\subseteq\{R_1,R_2\ge\tfrac12\}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 51, Example IV.8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Example IV.8, PDF pp.51-52: uniform Bell plus/minus ensemble. These are
necessary individual bounds, with no claim that the entire quadrant is achievable. -/
theorem eprSourceRegions :
    entanglementSourceRegion eprSource (by intros; rfl) ⊆ quantumSourceRegion eprSource ∧
    quantumSourceRegion eprSource ⊆ halfRateRegion := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
