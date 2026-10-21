-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_kraus_characterization
-- name    : QAlgorithms.Papers.Independent.Next46.P23.kraus_characterization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:51:37.493773+00:00
-- url     : https://prove2.me/theorems/aa76061c-f254-43b3-994a-da7990c6c59c
-- title:
--   Proposition 2.5
-- statement:
--   Let $\Phi:B(K)\to B(K^\prime)$ be complex-linear between nonzero finite-dimensional Hilbert spaces. It is completely positive exactly when it has a finite Kraus family $V_k:K\to K^\prime$ with $$\Phi(A)=\sum_k V_kAV_k^*.$$ For every such representation, unitality is equivalent to $\sum_kV_kV_k^*=I_{K^\prime}$ and trace preservation to $\sum_kV_k^*V_k=I_K$. No normalization condition is folded into complete positivity.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 40, Proposition 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Proposition2.5, Kraus characterization and both normalization conditions, source PDF p.40. -/
theorem kraus_characterization [Nonempty I] [Nonempty J] (Phi : Mat I →ₗ[ℂ] Mat J) :
    (QAlgorithms.Entanglement.IsCompletelyPositive Phi ↔
      ∃ r : ℕ, ∃ V : Fin r → Matrix J I ℂ,
        ∀ A, Phi A = ∑ k, V k * A * (V k)ᴴ) ∧
    (∀ r : ℕ, ∀ V : Fin r → Matrix J I ℂ,
      (∀ A, Phi A = ∑ k, V k * A * (V k)ᴴ) →
      (Phi 1 = 1 ↔ ∑ k, V k * (V k)ᴴ = 1) ∧
      ((∀ A, (Phi A).trace = A.trace) ↔ ∑ k, (V k)ᴴ * V k = 1)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
