-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_clonedCrossRegions
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.clonedCrossRegions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:49:15.248338+00:00
-- url     : https://prove2.me/theorems/a3ff535d-4088-4534-b897-5c73d4c03d9c
-- title:
--   Example IV.9: Uniform cloned cross {|00>,|11>}: Rq,Fe⊆{R1,R2≥1/2}, but Rq,Fbar={R1,R2≥0,R1+R2≥1}. Hence Rq,Fbar differs from Rq,Fe in general an
-- statement:
--   Consider the uniform cloned-cross ensemble $|00\rangle,|11\rangle$. It has the same average state as the Bell plus/minus source. Its quantum average-fidelity region is exact below, whereas only an outer bound is asserted for entanglement fidelity. In particular the two fidelity regions differ, and the average-fidelity region differs from that of the EPR ensemble despite their identical averages.
--
--   $$
--   \mathcal R_{q,F_e}\subseteq\{R_1,R_2\ge\tfrac12\},\quad\mathcal R_{q,\bar F}=\{R_1,R_2\ge0,\ R_1+R_2\ge1\},\quad\mathcal R_{q,F_e}\ne\mathcal R_{q,\bar F}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 52, Example IV.9

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

/-- Example IV.9, PDF p.52: same average as the EPR source, different ensemble.
No claim that the Fe region contains the half/half corner is made. -/
theorem clonedCrossRegions :
    entanglementSourceRegion clonedCross.multiple (by intros; rfl) ⊆ halfRateRegion ∧
    quantumSourceRegion clonedCross.multiple = nonnegativeSumRegion 1 ∧
    quantumSourceRegion clonedCross.multiple ≠
      entanglementSourceRegion clonedCross.multiple (by intros; rfl) ∧
    clonedCross.multiple.average = eprSource.average ∧
    quantumSourceRegion clonedCross.multiple ≠ quantumSourceRegion eprSource := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
