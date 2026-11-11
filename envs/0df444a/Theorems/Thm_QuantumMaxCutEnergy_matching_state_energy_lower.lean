-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_matching_state_energy_lower
-- name    : QuantumMaxCutEnergy.matching_state_energy_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:15:08.113235+00:00
-- url     : https://prove2.me/theorems/afc3c9cc-793c-46b6-aaa8-2bff5b865ab4
-- title:
--   Singlets on a matching give energy at least $(W+3\,w(M))/2$
-- statement:
--   Let $G$ be a graph on $n$ vertices with nonnegative rational edge weights $w$, and let $H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})$ with $\mathrm{OPT}(G)=\lambda_{\max}(H_G)$. For every matching $M$ (a set of pairwise vertex-disjoint pairs $i<j$),
--
--   $$\frac{W+3\,w(M)}{2}\le\mathrm{OPT}(G),\qquad W=\sum_{e}w_e,\quad w(M)=\sum_{e\in M}w_e.$$
--
--   The matching may use pairs of weight zero, and no maximality is assumed.
-- source:
--   Anshu, Gosset and Morenz, Beyond product state approximations for a quantum analogue of Max Cut, TQC 2020, https://doi.org/10.4230/LIPIcs.TQC.2020.7, Eq. (25); used as the matching-state bound in Lee and Parekh, ICALP 2024, https://doi.org/10.4230/LIPIcs.ICALP.2024.105, proof of Theorem 11 (Eq. (9)).

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators

theorem QuantumMaxCutEnergy.matching_state_energy_lower {n : ℕ}
    (w : QuantumMaxCutEnergy.Weights n) (M : Finset (QuantumMaxCutEnergy.Edge n))
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) :
    ((∑ e, (w e : ℝ)) + 3 * ∑ e ∈ M, (w e : ℝ)) / 2 ≤
      QuantumMaxCutEnergy.optimum ⟨n, w⟩ := by sorry
