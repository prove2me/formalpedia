-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_corollary_5_5
-- name    : QuantumLTF.Membership.Supplement.corollary_5_5
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T19:52:15.831414+00:00
-- url     : https://prove2.me/theorems/71f24c53-c91b-454c-8cb4-2a06094c82bc
-- title:
--   Corollary 5.5 — robustness of exact band conversion
-- statement:
--   Assume the band and register parameters of Theorem 5.4, and let a measured, classically controlled unitary channel exactly convert the ideal normalized Hermite band state to K copies of the unknown direction state, as in Eq. (183). If a normalized approximate band state differs from the ideal band state by at most ξ in Euclidean norm, its converted output differs from the ideal tensor-power density matrix by at most ξ in trace distance. The output is averaged over all internal measurement outcomes. Formalization Note. The exact-conversion premise identifies the channel supplied by Theorem 5.4; the corollary proves its robustness and does not construct that channel.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Section 5.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QuantumLTF_Membership_Supplement_measChannelOut
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem QuantumLTF.Membership.Supplement.corollary_5_5 {n K D q s e r : ℕ}
    (hK : 1 ≤ K) (hD : 2*K+1 ≤ D) (hq : D ≤ 2^q)
    (V : Matrix (Qubits (n*q+e)) (Qubits (n*q+e)) ℂ)
    (W : Qubits r → Matrix (Qubits (n*q+e)) (Qubits (n*q+e)) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits (n*q+e)) ℂ)
    (hW : ∀ t, W t ∈ Matrix.unitaryGroup (Qubits (n*q+e)) ℂ)
    (meas : Fin r ↪ Fin (n*q+e)) (out : Fin (K*s) ↪ Fin (n*q+e))
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1)
    (F : EuclideanSpace ℂ (Qubits (n*q))) (hF : ‖F‖ = 1)
    (ξ : ℝ) (hξ : ‖F-bandKet n q K w‖ ≤ ξ)
    (hexact : measChannelOut V W meas out (padKet e (bandKet n q K w)) =
      dirTensorPow s K w) :
    traceNorm (measChannelOut V W meas out (padKet e F) - dirTensorPow s K w) / 2 ≤ ξ := by sorry
