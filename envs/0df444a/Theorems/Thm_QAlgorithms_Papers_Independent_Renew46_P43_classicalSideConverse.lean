-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_classicalSideConverse
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.classicalSideConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:55:04.588139+00:00
-- url     : https://prove2.me/theorems/232ddcaf-42da-499d-a332-0ce3c45f02ad
-- title:
--   classical-side-information-lower: With classical side information only at quantum-source decoder, even Ra,Fbar(lambda)≥H(Y|X), every 0<lambda<1.
-- statement:
--   Let $(X,Y)$ be a finite correlated classical/fully quantum pure-letter source. Only the decoder receives $X^n$ for free; the arbitrary state-valued encoder sees the pure $Y$ word alone. The rate is the fixed-error limsup of operational block minima.
--
--   $$
--   R_{a,\bar F}^{\text{decoder-only }X}(\lambda)\ge H(Y\mid X),\qquad0<\lambda<1.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 56, classical-side-information-lower

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

/-- Unnumbered strong converse, PDF pp.56-57: even arbitrary encoding needs
H(Y|X) when free classical side information is available only at the decoder. -/
theorem classicalSideConverse (S : HybridSource 1)
    (hfull : ∀ a b, S.system.block a = S.system.block b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < 1) :
    classicalSideRate S false lambda ≥ ENNReal.ofReal
      (vnEntropy (S.marginal Finset.univ) - pmfEntropy
        (PMF.map (fun x => x.1 0) S.law)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
