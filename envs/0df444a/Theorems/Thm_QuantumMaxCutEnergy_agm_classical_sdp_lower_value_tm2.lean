-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm_classical_sdp_lower_value_tm2
-- name    : QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-01T17:36:36.20862+00:00
-- url     : https://prove2.me/theorems/d9f601e5-8c68-4369-a27d-701e73e686b8
-- title:
--   Polynomial-time TM2 certificate for a rational lower value of the Max-Cut SDP
-- statement:
--   For every weighted graph $G$ there is one nonnegative rational $L(G)$, computed by a single program that is polynomial-time in the multi-tape Turing-machine model (`Turing.TM2ComputableInPolyTime`) on the campaign's canonical graph-and-random-tape input encoding and its canonical nonnegative-rational output encoding, such that
--
--   $$L(G)\le S(G)\le L(G)+\frac{1}{10000}\sum_{\{i,j\}} w_{ij},$$
--
--   where $S(G)$ is the exact optimal value of the classical Max-Cut semidefinite relaxation of the symmetric weight matrix of $G$.
--
--   In words: the SDP value admits a genuine polynomial-time computable rational lower estimate with additive error at most $10^{-4}$ of the total edge weight, certified in the standard multi-tape model rather than in the library's Boolean-stack programming language. This is the numerical content of `QuantumMaxCutEnergy.agm_classical_sdp_lower_value_program` with the machine model factored out: the Boolean-stack compilation is supplied separately by `QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime`, which turns any polynomial-time TM2 certificate on the campaign encodings into a `PolyProgram` on the library ratio encoding. No solver, precision bound or probability assumption is asserted here beyond the existence of the machine.
-- source:
--   Reduction of QuantumMaxCutEnergy.agm_classical_sdp_lower_value_program: the numeric content of Anshu--Gosset--Morenz, TQC 2020, Theorem 3 (classical 0.53 approximation via the Max-Cut SDP, https://doi.org/10.4230/LIPIcs.TQC.2020.7), certified in the multi-tape Turing-machine model `Turing.TM2ComputableInPolyTime` of Mathlib 0df444a on the campaign encodings `QuantumMaxCutEnergy.encodeRequest` and `QuantumMaxCutEnergy.encodeValue`; the Boolean-stack compilation step is the separate platform lemma QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime (Mathlib's `Turing.TM2ComputableInPolyTime.comp` is a `proof_wanted` in that revision).

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
