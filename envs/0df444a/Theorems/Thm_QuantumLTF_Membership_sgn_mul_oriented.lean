-- Prove2me | Theorems.Thm_QuantumLTF_Membership_sgn_mul_oriented
-- name    : QuantumLTF.Membership.sgn_mul_oriented
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T03:19:25.018866+00:00
-- url     : https://prove2.me/theorems/c5bb3d46-a29f-4171-8e42-6877d05e9457
-- title:
--   Sign of an oriented product
-- statement:
--   For a nonzero real orientation coefficient $a$, multiplication by $a$ either preserves the sign convention (when $a$ is positive) or reverses it (when $a$ is negative).
-- source:
--   Supporting lemma for Section 3 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_sgn

theorem QuantumLTF.Membership.sgn_mul_oriented (a x : ℝ) (ha : a ≠ 0) :
    (if sgn a = 1 then sgn (a * x) = sgn x
     else sgn (a * x) = sgn (-x)) := by sorry
