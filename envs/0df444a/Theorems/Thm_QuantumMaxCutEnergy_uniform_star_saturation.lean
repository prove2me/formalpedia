-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_uniform_star_saturation
-- name    : QuantumMaxCutEnergy.uniform_star_saturation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T00:55:05.545739+00:00
-- url     : https://prove2.me/theorems/e3f43817-3ef7-4339-af27-bb2e1d724ae0
-- title:
--   Exact Quantum Max-Cut energy of a uniform star
-- statement:
--   Consider a star with center $c$ and $d\ge1$ leaves, all incident weights equal to one, with local terms $I-\mathrm{SWAP}_{ci}$. Every normalized state has energy at most $d+1$, and a normalized state attains that value:
--
--   $$\max_{\|\psi\|=1}\sum_{i\in S}\langle\psi,(I-\mathrm{SWAP}_{ci})\psi\rangle=d+1.$$
--
--   Additional spectator qubits are permitted. This is the saturation statement following the published Eq. (12).
-- source:
--   Anshu, Gosset, and Morenz, TQC 2020, p. 7:7, saturation remark immediately after Eq. (12), with upper bound Lemma 5 / Eq. (9). https://doi.org/10.4230/LIPIcs.TQC.2020.7 . Formal statement gives both the universal upper bound and attainment for every nonempty uniform star.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

theorem QuantumMaxCutEnergy.uniform_star_saturation {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (hc : c ∉ s) (hs : s.Nonempty) :
    (∀ ψ : QuantumMaxCutEnergy.Wave n, QuantumMaxCutEnergy.squaredNorm ψ = 1 →
      (∑ i ∈ s, (∑ x, Complex.normSq
        (ψ x - ψ (x ∘ Equiv.swap c i))) / 2) ≤ (s.card : ℝ) + 1) ∧
    ∃ ψ : QuantumMaxCutEnergy.Wave n, QuantumMaxCutEnergy.squaredNorm ψ = 1 ∧
      (∑ i ∈ s, (∑ x, Complex.normSq
        (ψ x - ψ (x ∘ Equiv.swap c i))) / 2) = (s.card : ℝ) + 1 := by sorry
