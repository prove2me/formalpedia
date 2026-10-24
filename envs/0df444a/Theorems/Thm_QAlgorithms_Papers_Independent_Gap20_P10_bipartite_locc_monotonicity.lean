-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_bipartite_locc_monotonicity
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.bipartite_locc_monotonicity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:24:54.742673+00:00
-- url     : https://prove2.me/theorems/f8a58c4e-876b-435c-ac74-035efd194206
-- title:
--   Deterministic and strong LOCC monotonicity
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   Let a finite adaptive LOCC protocol act on a bipartite state $\rho$. A deterministic output $\tau$ satisfies the first inequality below. If the protocol retains its outcomes, let $p_k$ and $\rho_k$ be its outcome probabilities and normalized conditional states. Then
--
--   $$E_I(\tau)\le E_I(\rho),\qquad \sum_k p_kE_I(\rho_k)\le E_I(\rho).$$
--
--   Local output dimensions may change. Instruments are complete and branches retain their full weights, including zero probabilities. These inequalities express the deterministic and average entanglement monotonicity.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 2, Unnumbered: deterministic and strong LOCC monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--3, axiom 1 and conclusion of (3): deterministic and strong
monotonicity under arbitrary finite adaptive LOCC, with normalized outcome
states and their full weights. Zero-weight branches require no division. -/
theorem bipartite_locc_monotonicity :
    (∀ s t : FiniteState 2, LOCC s [(1, t)] →
      cemiFunctional t ≤ cemiFunctional s) ∧
    IsAdaptiveLOCCMonotone (cemiFunctional (n := 2)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
