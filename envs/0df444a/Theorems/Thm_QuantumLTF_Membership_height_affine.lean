-- Prove2me | Theorems.Thm_QuantumLTF_Membership_height_affine
-- name    : QuantumLTF.Membership.height_affine
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T11:16:53.391281+00:00
-- url     : https://prove2.me/theorems/99df0ff0-6735-42a8-b853-00d9afd49981
-- title:
--   The boundary height is affine
-- statement:
--   Whenever the reference direction has nonzero inner product with the normal vector, the boundary-height function is affine in its displacement: its value at x equals its value at zero minus the directional inner product divided by the reference coefficient.
-- source:
--   Affine height identity used in Theorems 3.2 and 3.3 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_height

theorem QuantumLTF.Membership.height_affine {n : ℕ}
    (w p x : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (ha : inner ℝ w p ≠ 0) :
    height w θ p x = height w θ p 0 - inner ℝ w x / inner ℝ w p := by sorry
