-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_real_direction_recovery
-- name    : QuantumLTF.Membership.Supplement.real_direction_recovery
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T19:32:42.607108+00:00
-- url     : https://prove2.me/theorems/b0fbb663-6b17-434c-82a3-a4ac274c6adf
-- title:
--   Deterministic recovery of a real direction up to sign from a complex estimate
-- statement:
--   Let v be a complex unit vector, w a real unit vector, and 0 < ε < 1. If v is within ε/24 of a complex multiple ζw, take the larger-norm of the real and imaginary parts of v. This real vector r is nonzero, and its normalization is within ε/6 of either w or -w. The statement is stronger than the unit-phase version because no bound on ζ is needed. This is the deterministic phase-removal step in the proof of Theorem 5.6; choosing between the two signs still requires the orientation queries.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, proof of Theorem 5.6, Section 5.4.

import Mathlib

theorem QuantumLTF.Membership.Supplement.real_direction_recovery {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (w : EuclideanSpace ℝ (Fin n))
    (ζ : ℂ) (ε : ℝ) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hε : 0 < ε) (hε' : ε < 1)
    (hclose : ‖v - ζ • (WithLp.toLp 2 (fun i : Fin n => (w i : ℂ)) : EuclideanSpace ℂ (Fin n))‖ ≤ ε/24) :
    let a := (WithLp.toLp 2 (fun i : Fin n => (v i).re) : EuclideanSpace ℝ (Fin n))
    let b := (WithLp.toLp 2 (fun i : Fin n => (v i).im) : EuclideanSpace ℝ (Fin n))
    let r := if ‖b‖ ≤ ‖a‖ then a else b
    r ≠ 0 ∧
      (‖‖r‖⁻¹ • r - w‖ ≤ ε/6 ∨ ‖‖r‖⁻¹ • r + w‖ ≤ ε/6) := by sorry
