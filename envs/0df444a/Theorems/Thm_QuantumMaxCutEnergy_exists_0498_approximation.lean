-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_0498_approximation
-- name    : QuantumMaxCutEnergy.exists_0498_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-31T23:32:13.174437+00:00
-- url     : https://prove2.me/theorems/3aee3ec1-c508-4785-988a-96adadbd6a38
-- title:
--   A classical $0.498$ approximation of the Quantum Max-Cut energy
-- statement:
--   There exists one randomized classical polynomial-time algorithm that, for every finite graph with nonnegative rational edge weights, outputs a numerical estimate $v$ satisfying
--
--   $$0\le v\le\mathrm{OPT}(G)\quad\text{for every random outcome},\qquad\mathbb E[v]\ge 0.498\,\mathrm{OPT}(G).$$
--
--   Here $\mathrm{OPT}(G)=\lambda_{\max}(H_G)$ for $H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})$. The optimum ranges over all normalized quantum states. Both computation and the number of fair random bits are bounded by fixed polynomials in the encoded graph size. The output is a nonnegative rational number. The result includes empty graphs and zero weights. It is an expected approximation guarantee, not a per-outcome lower-ratio guarantee.
-- source:
--   Derived classical numerical guarantee from the peer-reviewed paper Anshu, Gosset, and Morenz, TQC 2020, Lemma 5 / Eq. (9) (weighted-star upper bound) and Eq. (25), p. 7:10 (matching energy W/2+3m/2), https://doi.org/10.4230/LIPIcs.TQC.2020.7 . The accepted proof combines these published ingredients with a concrete greedy matching and a verified rational Turing-machine implementation. It does not claim to formalize the paper's full 0.53 algorithm. The 0.498 target follows from the verified 1/2 guarantee by monotonicity; it is not a formalization of Gharibian–Parekh's SDP rounding algorithm. The historical 0.498 benchmark is published in https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.31 .

import Definitions.Def_QuantumMaxCutEnergyEstimationModel

theorem QuantumMaxCutEnergy.exists_0498_approximation :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.498 : ℝ) := by sorry
