-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_entropyOrdering
-- name    : QAlgorithms.Papers.Independent.Support50.P23.entropyOrdering
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:56:47.9591+00:00
-- url     : https://prove2.me/theorems/70c759ae-750d-4a71-91fe-53dab8853be7
-- title:
--   Ordering conditional min, von Neumann, and max entropies
-- statement:
--   For a normalized bipartite state $\rho_{AB}$ on finite-dimensional nonzero complex systems, let $H_{\min}$ be optimized over normalized reference states and let $H_{\max}$ be the purification-dual max entropy of Definition 2. Then, in bits,
--   $$
--   H_{\min}(A|B)_\rho\le H(A|B)_\rho\le H_{\max}(A|B)_\rho.
--   $$
--   Both inequalities are conclusions. This orders the paper's one-shot conditional entropies around their von Neumann counterpart.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 3, Lemma 2: ordering min, von Neumann, max

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

/-- Lemma 2, PDF p.3, (11): both inequalities, using Definition 2 max entropy. -/
theorem entropyOrdering [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    minEntropy rho ≤ (conditionalEntropyBitsAB rho : EReal) ∧
      (conditionalEntropyBitsAB rho : EReal) ≤ dualMaxEntropy rho := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
