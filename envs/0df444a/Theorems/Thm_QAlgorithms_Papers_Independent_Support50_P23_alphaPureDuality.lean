-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaPureDuality
-- name    : QAlgorithms.Papers.Independent.Support50.P23.alphaPureDuality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:59:42.996009+00:00
-- url     : https://prove2.me/theorems/2081cbb7-df0a-4651-b7a8-5e1a4b764606
-- title:
--   Pure-state fixed-reference alpha duality
-- statement:
--   Let $|\psi\rangle_{ABC}$ be a unit vector on finite-dimensional nonzero complex systems, let $\rho_{ABC}=|\psi\rangle\langle\psi|$, and compute all marginal states by partial trace. For every $\alpha\in[0,2]$,
--   $$
--   H_\alpha(A|B)_{\rho_{AB}|\rho_B}=-H_{2-\alpha}(A|C)_{\rho_{AC}|\rho_C}.
--   $$
--   This includes orders zero, one, and two. Both reference states come from the same pure state; the equality is the duality used in the max-entropy and AEP arguments.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 4, Lemma 6: pure-state alpha duality

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Lemma 6, PDF p.4, (21): references are marginals of the SAME normalized pure
state, including alpha=0,1,2. -/
theorem alphaPureDuality [Nonempty A] [Nonempty B] [Nonempty C]
    (psi : EuclideanSpace ℂ ((A × B) × C)) (hpsi : ‖psi‖ = 1)
    (alpha : ℝ≥0∞) (halpha : alpha ≤ 2) :
    alphaEntropy (traceRight (pureDensity psi))
      (traceLeft (traceRight (pureDensity psi))) alpha =
    -alphaEntropy (traceMiddleABC (pureDensity psi))
      (traceLeft (traceMiddleABC (pureDensity psi))) (2 - alpha) := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
