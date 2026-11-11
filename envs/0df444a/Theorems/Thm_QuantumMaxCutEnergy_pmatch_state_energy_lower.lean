-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_pmatch_state_energy_lower
-- name    : QuantumMaxCutEnergy.pmatch_state_energy_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:32:21.401998+00:00
-- url     : https://prove2.me/theorems/0767f3b0-20c3-4c1b-b585-a36ce1c57ecc
-- title:
--   Partially entangled matching state: energy $(1+\sin\theta)(1-t)/2$ on matched edges
-- statement:
--   Let $w$ be nonnegative rational edge weights on $n$ vertices, $r_1,\dots,r_n\in\mathbb R^3$ unit vectors with $t_{ij}=\langle r_i,r_j\rangle$, $M$ a matching, and $c,s$ real with $c^2+s^2=1$. Put $\sigma=2cs$ and $\kappa=c^2-s^2$ (so $\sigma=\sin\theta$, $\kappa=\cos\theta$ for $c=\cos\tfrac\theta2$). Then
--
--   $$\sum_{ij\in M}w_{ij}\,\frac{(1+\sigma)(1-t_{ij})}{2}+\sum_{ij\notin M}w_{ij}\,\frac{1-\kappa^2t_{ij}}{2}\le\lambda_{\max}\Bigl(\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})\Bigr).$$
--
--   The state is a product of two-qubit states $c\,|a_i\rangle|a_j\rangle+s\,e^{i\chi}|a_i^\perp\rangle|a_j^\perp\rangle$ on the matched pairs, whose marginal Bloch vectors are $\kappa r_i,\kappa r_j$, and of single-qubit states with Bloch vector $\kappa r_u$ on the unmatched vertices.
-- source:
--   Apte, Lee, Marwaha, Parekh and Sud, Conjectured Bounds for 2-Local Hamiltonians via Token Graphs / Improved Algorithms for Quantum MaxCut via Partially Entangled Matchings, ESA 2025, https://doi.org/10.4230/LIPIcs.ESA.2025.101, Lemma 5, Algorithm 2 and Lemma 9; arXiv:2504.15276v2, Lemma 5 (with depolarised unmatched qubits).

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators

theorem QuantumMaxCutEnergy.pmatch_state_energy_lower {n : ℕ}
    (w : QuantumMaxCutEnergy.Weights n) (r : Fin n → Fin 3 → ℝ)
    (hr : ∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1)
    (M : Finset (QuantumMaxCutEnergy.Edge n))
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (∑ e ∈ M, (w e : ℝ) * ((1 + 2 * c * s) *
        (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)) +
      (∑ e ∈ Finset.univ \ M, (w e : ℝ) *
        ((1 - (c ^ 2 - s ^ 2) ^ 2 * ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2)) ≤
      QuantumMaxCutEnergy.optimum ⟨n, w⟩ := by sorry
