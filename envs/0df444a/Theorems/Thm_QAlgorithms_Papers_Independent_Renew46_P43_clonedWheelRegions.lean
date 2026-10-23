-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_clonedWheelRegions
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.clonedWheelRegions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:46:23.670299+00:00
-- url     : https://prove2.me/theorems/2a860321-4726-4650-a8d1-063caac5d8c2
-- title:
--   Example IV.2: Uniform cloned wheel {|00>,|11>,|++>,|-->}: Rq,Fbar⊆{R1,R2≥1/2,R1+R2≥3/2}; Ra,Fbar={R1,R2≥0,R1+R2≥3/2}, so the regions can differ.
-- statement:
--   Consider the uniform cloned-wheel source with letters $|00\rangle,|11\rangle,|++\rangle,|--\rangle$, where $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$. The two encoders receive the same randomly chosen local pure state. Quantum encoding means separate local CPTP maps; arbitrary encoding may prepare a new state from the known local pure letter.
--
--   $$
--   \mathcal R_{q,\bar F}\subseteq\{R_1,R_2\ge\tfrac12,\ R_1+R_2\ge\tfrac32\},\quad\mathcal R_{a,\bar F}=\{R_1,R_2\ge0,\ R_1+R_2\ge\tfrac32\},\quad\mathcal R_{a,\bar F}\ne\mathcal R_{q,\bar F}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 47, Example IV.2

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

/-- Example IV.2, PDF pp.47-48: explicit uniform cloned-wheel ensemble. Only an
outer bound for quantum encoding is claimed; the arbitrary region is exact. -/
theorem clonedWheelRegions :
    quantumSourceRegion clonedWheel.multiple ⊆ wheelQuantumOuter ∧
    arbitrarySourceRegion clonedWheel = nonnegativeSumRegion (3/2) ∧
    arbitrarySourceRegion clonedWheel ≠ quantumSourceRegion clonedWheel.multiple := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
