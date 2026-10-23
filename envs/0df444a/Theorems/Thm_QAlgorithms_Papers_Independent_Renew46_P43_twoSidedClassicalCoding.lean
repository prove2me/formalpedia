-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_twoSidedClassicalCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.twoSidedClassicalCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:55:45.247665+00:00
-- url     : https://prove2.me/theorems/4488e777-c288-42ae-8980-5e1f44d39ed3
-- title:
--   two-sided-classical-side-information: If both encoder and decoder receive x^n, conditional quantum-source rate H(Y|X) is achievable with average fidelity→1.
-- statement:
--   For a finite correlated classical/fully quantum source $(X,Y)$, give $X^n$ to BOTH encoder and decoder. There are positive-dimensional block codes with a CPTP encoding conditional on each classical word, a CPTP decoder, and average fidelity $\bar F_n$ whose rates $R_n$ satisfy:
--
--   $$
--   R_n\longrightarrow H(Y\mid X),\qquad\bar F_n\longrightarrow1.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 57, two-sided-classical-side-information

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

/-- Unnumbered two-sided classical side-information scheme, PDF p.57. Its
encoder actually receives x^n; this is a different domain from the decoder-only model. -/
theorem twoSidedClassicalCoding (S : HybridSource 1)
    (hfull : ∀ a b, S.system.block a = S.system.block b) :
    ∃ c : ∀ n, ClassicalSideCode S (n+1) true,
      (∀ n x, ∃ E : Superop (Fin (n+1) → Fin S.system.dim) (Fin (c n).dim),
        IsChannel E ∧ ∀ p, E (wordTensor (fun t => S.letter (p t))) = (c n).encode x p) ∧
      Tendsto (fun n => Real.logb 2 (c n).dim / (n+1 : ℝ)) atTop
        (nhds (vnEntropy (S.marginal Finset.univ) -
          pmfEntropy (PMF.map (fun x => x.1 0) S.law))) ∧
      Tendsto (fun n => (c n).fidelity) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
