-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_measChannelOut_pad_stability
-- name    : QuantumLTF.Membership.Supplement.measChannelOut_pad_stability
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T19:52:03.769183+00:00
-- url     : https://prove2.me/theorems/4a50dcc0-74e7-4a20-bf2b-61c657a9d546
-- title:
--   Pure-input stability for measured channels with classical control and discarded registers
-- statement:
--   Apply any unitary, measure selected qubits, apply a unitary chosen from the measurement outcome, and discard all but a chosen output register. If both pure inputs are normalized, the trace distance between the outputs is at most the Euclidean distance between the original inputs. Appending the same clean ancillas does not alter the bound. The output averages over all measurement outcomes; this guarantee needs no postselection and incurs no additional success-probability loss. This is the quantitative channel-stability statement used in Corollary 5.5.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Section 5.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QuantumLTF_Membership_Supplement_measChannelOut
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
open QAlgorithms QuantumLTF.Membership.Supplement

theorem QuantumLTF.Membership.Supplement.measChannelOut_pad_stability {N e r o : ℕ}
    (V : Matrix (Qubits (N+e)) (Qubits (N+e)) ℂ)
    (W : Qubits r → Matrix (Qubits (N+e)) (Qubits (N+e)) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits (N+e)) ℂ)
    (hW : ∀ t, W t ∈ Matrix.unitaryGroup (Qubits (N+e)) ℂ)
    (meas : Fin r ↪ Fin (N+e)) (out : Fin o ↪ Fin (N+e))
    (ψ φ : EuclideanSpace ℂ (Qubits N)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (measChannelOut V W meas out (padKet e ψ) -
      measChannelOut V W meas out (padKet e φ)) / 2 ≤ ‖ψ-φ‖ := by sorry
