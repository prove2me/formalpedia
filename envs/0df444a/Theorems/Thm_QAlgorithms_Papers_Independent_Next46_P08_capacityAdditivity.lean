-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P08_capacityAdditivity
-- name    : QAlgorithms.Papers.Independent.Next46.P08.capacityAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:55:48.603403+00:00
-- url     : https://prove2.me/theorems/90e17354-36d3-490f-9f29-b63f299317b6
-- title:
--   Capacity additivity implies equality of classical and Holevo capacities
-- statement:
--   Let $\Phi:A\to B$ be a quantum channel between infinite-dimensional separable complex systems. Let $H_A$ be any positive densely defined self-adjoint input Hamiltonian and let $E\ge E_0^A$, its spectral infimum. Write $C_\chi(\Phi,H_A,E)$ for the extended supremum of output Holevo information over all finite or countable input ensembles whose computed barycenter has energy at most $E$. Let $H_A^{(n)}=\sum_{k=1}^n H_{A_k}$ be the additive block Hamiltonian, and define the regularized classical capacity by the source limit of $n^{-1}C_\chi(\Phi^{\otimes n},H_A^{(n)},nE)$.
--
--   If for every $n\ge1$,
--
--   $$
--   C_\chi(\Phi^{\otimes n},H_A^{(n)},nE)=n\,C_\chi(\Phi,H_A,E),
--   $$
--
--   then
--
--   $$
--   C(\Phi,H_A,E)=C_\chi(\Phi,H_A,E).
--   $$
--
--   All capacities are extended nonnegative values, so infinite capacities and an empty ground-energy feasible set are retained. No Gibbs, output-energy or finiteness assumption is imposed. The statement concerns actual constrained capacities, rather than an independently supplied numerical sequence.
-- source:
--   Energy-constrained diamond norms and their use in quantum information theory, arXiv:1706.00361v2, PDF p. 14, §5.3, equation (20): capacity equality under additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P08

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P08

export QAlgorithms.Papers.Independent.Claimed50.P32 (StrongChannel)

export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble ensembleHolevo)

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Section 5.3, PDF p.14, equation (20): all-positive-block additivity of the
ACTUAL constrained Holevo capacity implies equality of regularized classical
and single-use Holevo capacities. Infinite capacity is retained; no Gibbs,
output-energy or finiteness hypothesis is imposed. The ground endpoint remains. -/
theorem capacityAdditivity (H : Forms.PositiveObservable ℕ) (E : ℝ)
    (hE : formGroundEnergy H ≤ E) (Phi : StrongChannel ℕ ℕ)
    (hadd : ∀ n : ℕ, 0 < n → blockConstrainedChi H E Phi n =
      (n : ℝ≥0∞) * constrainedChi H E Phi) :
    constrainedClassical H E Phi = constrainedChi H E Phi := by sorry

end QAlgorithms.Papers.Independent.Next46.P08

end
