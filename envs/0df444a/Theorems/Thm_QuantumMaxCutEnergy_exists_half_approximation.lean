-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_half_approximation
-- name    : QuantumMaxCutEnergy.exists_half_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-31T23:32:33.700177+00:00
-- url     : https://prove2.me/theorems/d1db72f7-5b4d-471a-8cb5-603aeff6b379
-- title:
--   A classical $1/2$ approximation of the Quantum Max-Cut energy
-- statement:
--   There exists one randomized classical polynomial-time algorithm that, for every finite graph with nonnegative rational edge weights, outputs a numerical estimate $v$ satisfying
--
--   $$0\le v\le\mathrm{OPT}(G)\quad\text{for every random outcome},\qquad\mathbb E[v]\ge 0.5\,\mathrm{OPT}(G).$$
--
--   Here $\mathrm{OPT}(G)=\lambda_{\max}(H_G)$ for $H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})$. The optimum ranges over all normalized quantum states. Both computation and the number of fair random bits are bounded by fixed polynomials in the encoded graph size. The output is a nonnegative rational number. The result includes empty graphs and zero weights. It is an expected approximation guarantee, not a per-outcome lower-ratio guarantee.
-- source:
--   Derived classical numerical guarantee from the peer-reviewed paper Anshu, Gosset, and Morenz, TQC 2020, Lemma 5 / Eq. (9) (weighted-star upper bound) and Eq. (25), p. 7:10 (matching energy W/2+3m/2), https://doi.org/10.4230/LIPIcs.TQC.2020.7 . The accepted proof combines these published ingredients with a concrete greedy matching and a verified rational Turing-machine implementation. It does not claim to formalize the paper's full 0.53 algorithm.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel

theorem QuantumMaxCutEnergy.exists_half_approximation :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.5 : ℝ) := by sorry
