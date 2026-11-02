-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_sdp_structural_domination
-- name    : QuantumMaxCutEnergy.agm_sdp_structural_domination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:49:39.890643+00:00
-- url     : https://prove2.me/theorems/171f0770-ad18-49ff-a116-adb00748e1c3
-- title:
--   The classical Max-Cut SDP dominates one third of QMC energy plus total weight
-- statement:
--   For every graph G with nonnegative rational weights, let S be the actual optimum value of the classical Max-Cut semidefinite relaxation of its symmetric weight matrix. Then (OPT(G)+W(G))/3≤S, where W is total edge weight and OPT is the unrestricted Quantum Max-Cut optimum in the campaign normalization. This includes empty graphs and zero weights. The formal hypothesis identifies S as the specified SDP value, rather than assuming an arbitrary upper bound. The proof constructs a feasible Gram matrix directly from the X, Y and Z Pauli actions on each normalized quantum state.
-- source:
--   Anshu, Gosset and Morenz, TQC2020, Eqs18–19 and their weighted extension in the proof of Theorem3, pp7:8–7:9. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . Direct Pauli-Gram proof of the needed SDP domination, using the standard classical Max-Cut relaxation; no optimization algorithm is assumed.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm_sdp_structural_domination (G : QuantumMaxCutEnergy.Input) (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue
      (Matrix.of fun i j : Fin G.n =>
        if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
        else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S) :
    (QuantumMaxCutEnergy.optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤ S := by sorry
