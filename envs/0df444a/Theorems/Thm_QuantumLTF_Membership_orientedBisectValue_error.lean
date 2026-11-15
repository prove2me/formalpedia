-- Prove2me | Theorems.Thm_QuantumLTF_Membership_orientedBisectValue_error
-- name    : QuantumLTF.Membership.orientedBisectValue_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T03:04:24.138237+00:00
-- url     : https://prove2.me/theorems/ad6e5167-fb67-4b88-b8a2-d1963de69478
-- title:
--   Error bound for oriented bisection
-- statement:
--   Starting from an interval $[lo,hi]$ containing the threshold $h$, after $q$ orientation-aware bisection updates the returned midpoint differs from $h$ by at most $(hi-lo)/2^{q+1}$. The statement handles both positive and negative orientations.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, pp. 21–22 (PDF pp. 22–23).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue

namespace QuantumLTF.Membership

/-- After `q` oriented bisection updates, the returned midpoint has exponentially small error. -/
theorem orientedBisectValue_error (s : ℤ) (q : ℕ) (lo hi h : ℝ)
    (hlo : lo ≤ h) (hhi : h ≤ hi) :
    |orientedBisectValue s q lo hi h - h| ≤
      (hi - lo) / (2 : ℝ) ^ (q + 1) := by sorry

end QuantumLTF.Membership
