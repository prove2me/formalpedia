-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_physical_state_upper_bound
-- name    : QuantumMaxCutEnergy.PauliSDP.physical_state_upper_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:27:42.190437+00:00
-- url     : https://prove2.me/theorems/09a6a98b-2702-4a7b-9433-0aacda441280
-- title:
--   Every finite Pauli relaxation bounds Quantum Max-Cut energy from above
-- statement:
--   For every graph $G$ with nonnegative rational edge weights and every hierarchy level $k\ge2$,
--
--   $$\mathrm{OPT}(G)\le U_k(G).$$
--
--   Here $U_k(G)$ is the value of the canonical Pauli moment relaxation, with the same Hamiltonian normalization as the campaign.
-- source:
--   Gribling, Sinjorgo and Sotirov, arXiv:2504.11120v1, Section 2, Eqs. (2.3)–(2.4): https://arxiv.org/html/2504.11120v1#S2 ; Gharibian and Parekh, APPROX/RANDOM 2019: https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.31 . The campaign Hamiltonian is half of Eq. (1.1) in GSS; its Pauli objective therefore includes the factor 1/2.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel

open scoped BigOperators

theorem QuantumMaxCutEnergy.PauliSDP.physical_state_upper_bound (k : ℕ) (hk : 2 ≤ k) (G : QuantumMaxCutEnergy.Input) :
    QuantumMaxCutEnergy.optimum G ≤ QuantumMaxCutEnergy.PauliSDP.value k G := by sorry
