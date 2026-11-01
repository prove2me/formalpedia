-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_weighted_star_energy_upper_bound
-- name    : QuantumMaxCutEnergy.weighted_star_energy_upper_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T00:27:13.403329+00:00
-- url     : https://prove2.me/theorems/24ae227c-c3e9-4a76-a90d-a52befd63179
-- title:
--   Weighted-star upper bound for Quantum Max-Cut
-- statement:
--   Let $c$ be the center of a star and $S$ its set of leaves, with $c\notin S$. Assign each leaf a nonnegative real edge weight $w_i$, and let $M\ge0$ bound every weight. For every normalized $n$-qubit state $\psi$,
--
--   $$\sum_{i\in S}w_i\langle\psi,(I-\mathrm{SWAP}_{ci})\psi\rangle\le\sum_{i\in S}w_i+M.$$
--
--   Thus the optimum energy of a weighted star is at most its total edge weight plus its largest edge weight. Additional qubits and entanglement with them are allowed. This is a supporting energy bound; it does not assert an approximation algorithm.
-- source:
--   Anurag Anshu, David Gosset, and Karen Morenz. Beyond Product State Approximations for a Quantum Analogue of Max Cut. TQC 2020, LIPIcs 158, Article 7, Lemma 5, Eq. (9), pp. 7:6–7:7. Published primary source: https://doi.org/10.4230/LIPIcs.TQC.2020.7 ; PDF: https://drops.dagstuhl.de/storage/00lipics/lipics-vol158-tqc2020/LIPIcs.TQC.2020.7/LIPIcs.TQC.2020.7.pdf . The formal statement uses an arbitrary nonnegative upper bound M on star weights and the same I - SWAP normalization.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib.Tactic

theorem QuantumMaxCutEnergy.weighted_star_energy_upper_bound {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : QuantumMaxCutEnergy.Wave n) (M : ℝ)
    (hc : c ∉ s) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hM0 : 0 ≤ M) (hM : ∀ i ∈ s, w i ≤ M)
    (hψ : QuantumMaxCutEnergy.squaredNorm ψ = 1) :
    (∑ i ∈ s, w i / 2 * (∑ x, Complex.normSq
      (ψ x - ψ (x ∘ Equiv.swap c i)))) ≤ (∑ i ∈ s, w i) + M := by sorry
