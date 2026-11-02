-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_0531_approximation
-- name    : QuantumMaxCutEnergy.exists_0531_approximation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-01T14:02:28.182437+00:00
-- url     : https://prove2.me/theorems/78609b23-1bdd-46e1-84d6-d64e67fc2f59
-- title:
--   Classical 0.531 approximation of Quantum Max-Cut energy
-- statement:
--   There exists one uniform randomized classical polynomial-time algorithm that, for every finite graph $G$ with nonnegative rational edge weights, returns a nonnegative rational estimate $v(G,R)$ using its internal fair random bits $R$. For each fixed input graph,
--
--   $$0\le v(G,R)\le\mathrm{OPT}(G)\quad\text{for every prescribed random tape }R,$$
--
--   $$\mathbb E_R[v(G,R)]\ge 0.531\,\mathrm{OPT}(G).$$
--
--   Here $\mathrm{OPT}(G)=\lambda_{\max}(H_G)$ for $H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})$, with the optimum over all normalized quantum states. The expectation is the uniform finite average over the algorithm's prescribed polynomial-length random tapes, separately for every input. Running time is polynomial on every run. This is an expected approximation ratio; a high-probability ratio would require an additional probability statement. Empty graphs and zero weights are included.
-- source:
--   AGM20; general-graph benchmark 0.531 in https://marwahaha.github.io/quantum-maxcut-reference/problems/qmc. The QMC reference attributes this value to Anshu, Gosset and Morenz (TQC 2020). Their printed Theorem 3 states 0.53; the 0.531 target refines the published three-candidate bound in Eq. (30), as also reported by later published work. Sources: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TQC.2020.7. The exact finite-bit classical energy-estimation statement is the campaign target; it is not an assertion that the cited construction has been formalized.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel

theorem QuantumMaxCutEnergy.exists_0531_approximation :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.531 : ℝ) := by sorry
