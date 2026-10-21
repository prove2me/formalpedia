-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_unrestrictedCqCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.unrestrictedCqCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:32:34.246253+00:00
-- url     : https://prove2.me/theorems/6e9af459-8e05-4861-a6e6-aaacd2048961
-- title:
--   Theorem 3: unrestricted c-q coding theorem
-- statement:
--   Let $a\mapsto S_a$ be a memoryless c-q alphabet of normalized positive trace-class operators on a nonzero complex Hilbert space. The alphabet and dimension may be infinite. Assume one finite uniform upper bound on the individual entropies $H(S_a)$. Then
--
--   $$C=\bar C=\sup_\pi\sum_a\pi_a D(S_a\Vert\bar S_\pi),\qquad\bar S_\pi=\sum_a\pi_a S_a.$$
--
--   The supremum ranges over all discrete probability laws. Capacity uses product-letter codes, arbitrary collective bounded sub-POVMs, uniform average error, and natural logarithms. Infinite capacity remains allowed. This is the unrestricted c-q coding theorem.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 16, Theorem 3: unrestricted c-q coding theorem

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3, PDF pp.16-17, (48): unrestricted alphabet, full output space,
uniformly bounded individual entropies, and possibly infinite capacity. -/
theorem unrestrictedCqCoding {A I : Type} [Nonempty A] [Nonempty I]
    (S : A → Matrix I I ℂ) (hS : ∀ a, TC.IsDensity (S a))
    (hentropy : BoundedLetterEntropy S) :
    averageErrorCqCapacity S (fun _ => 0) 0 = cqHolevoCapacity S (fun _ => 0) 0 ∧
    averageErrorCqCapacity S (fun _ => 0) 0 = ⨆ pi : DiscreteInputLaw A, discreteHolevoInformation S pi := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
