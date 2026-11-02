-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_053_from_rank_three_gap_and_sdp_program
-- name    : QuantumMaxCutEnergy.exists_053_from_rank_three_gap_and_sdp_program
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T16:56:34.764042+00:00
-- url     : https://prove2.me/theorems/8b0ceb43-54eb-497b-bcb9-bd93faeeeb6a
-- title:
--   0.53 Quantum Max-Cut energy estimation from the rank-three gap and a certified SDP lower-value program
-- statement:
--   Let G be a finite graph with nonnegative rational edge weights, H_G = sum w_ij (I - SWAP_ij), and OPT(G) the largest expected energy of H_G. Suppose (i) the rank-three gap holds: for every graph G and every value S of the classical Max-Cut semidefinite relaxation, 0.954*S <= OPT(G); and (ii) there is a deterministic finite Boolean polynomial-time program L with L(G) <= S <= L(G) + W/10000, where W is the total edge weight and S is that relaxation value. Then there is a randomized classical polynomial-time algorithm whose every output is at most OPT(G) and whose expected output is at least 0.53*OPT(G).
-- source:
--   Anshu, Gosset, Morenz, TQC 2020, Theorem 3, https://doi.org/10.4230/LIPIcs.TQC.2020.7 pp. 7:9-7:10; Briet, de Oliveira Filho, Vallentin 2014, Lemma 2.1. This entry records the verified reduction step between the campaign's open milestones (rank-three gap, certified SDP lower-value program) and its root theorem; not a verbatim statement in either source.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.exists_053_from_rank_three_gap_and_sdp_program
    (hgap : ∀ (G : QuantumMaxCutEnergy.Input) (S : ℝ),
      ModernConvex.Relaxations.IsMaxcutSDPValue
        (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S →
      (0.954 : ℝ) * S ≤ QuantumMaxCutEnergy.optimum G)
    (hprog : ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (OAI.MetricKMedian.Binary.PolyProgram
        QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
        (fun request : QuantumMaxCutEnergy.Input × List Bool => (L request.1 : ℚ))) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧ S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.53 : ℝ) := by sorry
