-- Prove2me | Theorems.Thm_QuantumLTF_Membership_strict_orientation_sign
-- name    : QuantumLTF.Membership.strict_orientation_sign
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T02:59:54.659057+00:00
-- url     : https://prove2.me/theorems/4d31e7a8-2a26-4879-bc2d-7b6a0dcaa7e1
-- title:
--   Strict endpoint queries determine threshold orientation
-- statement:
--   If the scalar threshold $h$ lies in $[-L,L]$ and the nonzero orientation is $a$, then querying the oriented threshold at $L+1$ and $-(L+1)$ identifies $sign(a)$ exactly. Strictly exterior queries avoid ambiguity from the convention $sign(0)=1$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, pp. 21–22 (PDF pp. 22–23).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_sgn

namespace QuantumLTF.Membership

/-- Queries strictly beyond a promised boundary interval determine the sign of the orientation. -/
theorem strict_orientation_sign (a h L : ℝ) (ha : a ≠ 0) (hh : |h| ≤ L) :
    (if sgn (a * ((L + 1) - h)) = 1 ∧
        sgn (a * (-(L + 1) - h)) = -1 then 1 else -1) =
      sgn a := by sorry

end QuantumLTF.Membership
