-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_rank_three_rounding_pointwise
-- name    : QuantumMaxCutEnergy.rank_three_rounding_pointwise
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-01T16:59:07.777882+00:00
-- url     : https://prove2.me/theorems/f0c9b488-657c-4149-aaab-da164a74ba2f
-- title:
--   Pointwise rank-three rounding bound for the classical Max-Cut relaxation
-- statement:
--   Let $G$ be a weighted graph on $n$ vertices with nonnegative rational edge weights, put $w_{ij}=w_{ji}$ on adjacent pairs and $0$ elsewhere, and let $X$ be a feasible matrix of the classical Max-Cut semidefinite relaxation: $X$ symmetric positive semidefinite with all diagonal entries equal to $1$. Then there is a normalized Quantum Max-Cut state whose energy is at least
--
--   $$0.954\cdot \frac14\sum_{i,j} w_{ij}\,(1-X_{ij}) .$$
--
--   Equivalently, the scaled classical relaxation objective of every feasible $X$ is at most the Quantum Max-Cut optimum of $G$.
--
--   This is the pointwise rank-three rounding obligation isolated from the campaign's target $0.954\,S\le \mathrm{OPT}$, where $S$ is the optimal relaxation value: the order-theoretic passage from the supremum to the pointwise statement is proved separately, so what remains here is exactly the analytic content of Theorem 1 of Anshu--Gosset--Morenz together with Lemma 2.1 of Brie\u0308t--de Oliveira Filho--Vallentin. No rounding scheme, sampler or numerical solver is assumed; the factor $0.954$ leaves slack below the published $0.956$ rank-three guarantee.
--
--   Formalization note: the statement is a per-instance implication, with $X$ universally quantified inside the graph, so a proof may construct any state it likes; the campaign energy convention is $h_{ij}=I-\mathrm{SWAP}_{ij}$.
-- source:
--   Anshu, Gosset, Morenz, TQC 2020, Theorem 1 and Lemma 2.1 of Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4) 2014, https://doi.org/10.4086/toc.2014.v010a004 ; the 0.954 factor is a weaker target than the published 0.956 guarantee. Isolated pointwise form of the campaign leaf agm_classical_sdp_rank_three_gap.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.rank_three_rounding_pointwise
    (G : QuantumMaxCutEnergy.Input) (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    (0.954 : ℝ) * ModernConvex.Relaxations.maxcutRelaxationObjective
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) X
      ≤ QuantumMaxCutEnergy.optimum G := by sorry
