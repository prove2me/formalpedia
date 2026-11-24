-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_dirTensorPow_state
-- name    : QuantumLTF.Membership.Supplement.dirTensorPow_state
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T19:32:53.229977+00:00
-- url     : https://prove2.me/theorems/a0817745-ea81-41e8-84a5-70c977ef6262
-- title:
--   The direction tensor power is a normalized density operator on the promised label span
-- statement:
--   For every real unit vector w, every number K of copies, and every binary register width s with n ≤ 2^s, the explicit matrix dirTensorPow s K w is positive semidefinite, has trace one, and is supported on the tensor product of the first n binary labels. This proves the physical validity and support certificates for the ideal tomography input in Theorem 5.6, including K=0 and arbitrary padding in the labels.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 5.4, Eq. (187).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_IsStateOnSpan
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem QuantumLTF.Membership.Supplement.dirTensorPow_state {n s K : ℕ} (h : n ≤ 2^s)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    IsStateOnSpan n s K (dirTensorPow s K w) := by sorry
