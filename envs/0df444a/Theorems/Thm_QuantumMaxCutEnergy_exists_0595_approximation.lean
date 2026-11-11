-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_0595_approximation
-- name    : QuantumMaxCutEnergy.exists_0595_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:02:59.462884+00:00
-- url     : https://prove2.me/theorems/4d770c30-7798-4486-8db7-94e92888ff01
-- title:
--   Classical 0.595 approximation of Quantum Max-Cut energy
-- statement:
--   There exists one uniform randomized classical polynomial-time algorithm that, for every finite graph $G$ with nonnegative rational edge weights, returns a nonnegative rational estimate $v(G,R)$ using its internal fair random bits $R$. For each fixed input graph,
--
--   $$0\le v(G,R)\le\mathrm{OPT}(G)\quad\text{for every prescribed random tape }R,$$
--
--   $$\mathbb E_R[v(G,R)]\ge 0.595\,\mathrm{OPT}(G).$$
--
--   Here $\mathrm{OPT}(G)=\lambda_{\max}(H_G)$ for $H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})$, with the optimum over all normalized quantum states. The expectation is the uniform finite average over the algorithm's prescribed polynomial-length random tapes, separately for every input. Running time is polynomial on every run. This is an expected approximation ratio; a high-probability ratio would require an additional probability statement. Empty graphs and zero weights are included.
-- source:
--   LP24; general-graph benchmark 0.595 in https://marwahaha.github.io/quantum-maxcut-reference/problems/qmc. Lee and Parekh (ICALP 2024), Theorem 11, obtain this expected guarantee by combining GP rounding with a maximum-matching state. Sources: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.105. The exact finite-bit classical energy-estimation statement is the campaign target; it is not an assertion that the cited construction has been formalized.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel

theorem QuantumMaxCutEnergy.exists_0595_approximation :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.595 : ℝ) := by sorry
