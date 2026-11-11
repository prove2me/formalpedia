-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_0603_approximation
-- name    : QuantumMaxCutEnergy.exists_0603_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:03:10.222832+00:00
-- url     : https://prove2.me/theorems/6de7f189-869d-4015-b078-4355c5c8012b
-- title:
--   Classical 0.603 approximation of Quantum Max-Cut energy
-- statement:
--   There exists one uniform randomized classical polynomial-time algorithm that, for every finite graph $G$ with nonnegative rational edge weights, returns a nonnegative rational estimate $v(G,R)$ using its internal fair random bits $R$. For each fixed input graph,
--
--   $$0\le v(G,R)\le\mathrm{OPT}(G)\quad\text{for every prescribed random tape }R,$$
--
--   $$\mathbb E_R[v(G,R)]\ge 0.603\,\mathrm{OPT}(G).$$
--
--   Here $\mathrm{OPT}(G)=\lambda_{\max}(H_G)$ for $H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})$, with the optimum over all normalized quantum states. The expectation is the uniform finite average over the algorithm's prescribed polynomial-length random tapes, separately for every input. Running time is polynomial on every run. This is an expected approximation ratio; a high-probability ratio would require an additional probability statement. Empty graphs and zero weights are included.
-- source:
--   GSS25; general-graph benchmark 0.603 in https://marwahaha.github.io/quantum-maxcut-reference/problems/qmc. The QMC reference attributes this value to Gribling, Sinjorgo and Sotirov’s improved Lee–Parekh analysis using a level-13 sum-of-squares matching bound. The cited work is a public preprint. Sources: https://arxiv.org/abs/2504.11120. The exact finite-bit classical energy-estimation statement is the campaign target; it is not an assertion that the cited construction has been formalized.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel

theorem QuantumMaxCutEnergy.exists_0603_approximation :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.603 : ℝ) := by sorry
