-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P08_blockEnergySymmetrization
-- name    : QAlgorithms.Papers.Independent.Next46.P08.blockEnergySymmetrization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:57:05.659812+00:00
-- url     : https://prove2.me/theorems/3c0e1e52-f92d-4029-96c3-efe65215a91f
-- title:
--   Block Holevo supremum equals the per-site barycenter-constrained supremum
-- statement:
--   Let $\Phi:A\to B$ be a channel between infinite-dimensional separable complex systems, let $H_A$ be a positive densely defined self-adjoint Hamiltonian with spectral infimum $E_0^A$, let $E\ge E_0^A$, and let $n\ge1$. For any finite or countable ensemble $\mathcal E=\{p_i,\rho_i\}$ of states on $A^{\otimes n}$, write $\bar\rho=\sum_i p_i\rho_i$ for its actual barycenter. Then
--
--   $$
--   C_\chi(\Phi^{\otimes n},H_A^{(n)},nE)
--   =\sup_{\mathcal E:\ \operatorname{Tr}H_A\bar\rho_{A_k}\le E\ \forall k=1,\ldots,n}
--   \chi\bigl(\{p_i,\Phi^{\otimes n}(\rho_i)\}\bigr).
--   $$
--
--   The left side optimizes under the total additive energy bound $nE$. The right side constrains every single-site marginal of the barycenter, with no constraint on individual ensemble members. This equality justifies applying a fixed-input-energy channel bound at each site without assuming an optimizing ensemble exists. Both suprema are extended nonnegative values, equal to zero if their feasible sets are empty.
-- source:
--   Energy-constrained diamond norms and their use in quantum information theory, arXiv:1706.00361v2, PDF p. 15, Proposition 6 proof: equal per-site block constraint

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P08

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P08

export QAlgorithms.Papers.Independent.Claimed50.P32 (StrongChannel)

export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble ensembleHolevo)

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Proposition 6 proof, PDF pp.15–16: total-energy and equal-per-site
barycenter constraints have the same Holevo supremum for every positive block
length. The statement uses actual ensembles and channels and does not assume
attainment. General positive observables and an empty ground feasible set are
allowed; nonnegative extended empty suprema equal zero. -/
theorem blockEnergySymmetrization (H : Forms.PositiveObservable ℕ) (E : ℝ)
    (hE : formGroundEnergy H ≤ E) (Phi : StrongChannel ℕ ℕ) (n : ℕ) (hn : 0 < n) :
    blockConstrainedChi H E Phi n = perSiteConstrainedChi H E Phi n := by sorry

end QAlgorithms.Papers.Independent.Next46.P08

end
