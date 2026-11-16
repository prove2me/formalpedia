-- Prove2me | Theorems.Thm_QuantumLTF_Membership_ltf_line_eq_height_sign
-- name    : QuantumLTF.Membership.ltf_line_eq_height_sign
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T11:29:45.516825+00:00
-- url     : https://prove2.me/theorems/c42685ba-2229-4cff-bb0a-f9428f387370
-- title:
--   Membership queries along the reference line locate the height
-- statement:
--   Along the affine line through x in reference direction p, a linear-threshold membership query is the oriented sign of the scalar displacement from the boundary height at x.
-- source:
--   Line-query identity used by the coherent height oracle in Theorem 3.2 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height

theorem QuantumLTF.Membership.ltf_line_eq_height_sign {n : ℕ}
    (w p x : EuclideanSpace ℝ (Fin n)) (θ t : ℝ)
    (ha : inner ℝ w p ≠ 0) :
    ltf w θ (x + t • p) =
      sgn (inner ℝ w p * (t - height w θ p x)) := by sorry
