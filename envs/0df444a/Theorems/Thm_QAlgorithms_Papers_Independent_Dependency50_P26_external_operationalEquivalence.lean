-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_external_operationalEquivalence
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.external_operationalEquivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:34:03.055974+00:00
-- url     : https://prove2.me/theorems/d0423f6d-fee6-4f2c-85b2-11aa50a6d7f9
-- title:
--   §III C.5: generalized Born rule and operational equivalence
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $R,S$ be the Choi operators of two deterministic or probabilistic networks with the same ordered external wires, represented by positive combs dominated by deterministic combs. If $R=S$, every external tester $\{P_i\}$ gives identical outcome probabilities. The entrywise full link contraction obeys the generalized Born rule
--
--   $$
--   p(i\mid R)=\operatorname{Re}\operatorname{Tr}(P_i^T R).
--   $$
--
--   For a probabilistic network these are joint outcome weights, including the success of its branch. Only external input/output experiments are compared.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 9, §III C.5: generalized Born rule and operational equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.9, Eq.(38): generalized Born rule and forward operational equivalence for
external experiments on deterministic or probabilistic networks. Their Choi operators
are probabilistic combs (Definition 4); deterministic combs are included by taking
themselves as their deterministic upper bound. Only external input/output experiments
are compared, as specified in the source. -/
theorem external_operationalEquivalence (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s n) (Basis s n) ℂ) (hP : CombTester s n k P)
    (R S : Matrix (Basis s n) (Basis s n) ℂ)
    (hR : Probabilistic s n R) (hS : Probabilistic s n S) (h : R = S) :
    (∀ i, externalProbability s n R (P i) = QAlgorithms.effectProb (P i).transpose R) ∧
      (∀ i, externalProbability s n R (P i) = externalProbability s n S (P i)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
