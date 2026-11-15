-- Prove2me | Theorems.Thm_QuantumLTF_Membership_ltf_smul_eq_height_sign
-- name    : QuantumLTF.Membership.ltf_smul_eq_height_sign
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T02:47:23.738925+00:00
-- url     : https://prove2.me/theorems/2bea8678-e97c-4fa9-94d9-4f6a75bb5dbc
-- title:
--   LTF queries along the reference direction
-- statement:
--   When the reference correlation $a=inner(w,p)$ is nonzero, restricting the threshold function to points $tp$ yields the one-dimensional oriented threshold $sign(a(t-h_p(0)))$. Thus the boundary along this line is exactly $t=h_p(0)$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, pp. 21–22 (PDF pp. 22–23).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height

namespace QuantumLTF.Membership

/-- Restricting the LTF to the line through `p` gives an oriented scalar threshold at `height w θ p 0`. -/
theorem ltf_smul_eq_height_sign {n : ℕ} (w p : EuclideanSpace ℝ (Fin n))
    (θ t : ℝ) (ha : inner ℝ w p ≠ 0) :
    ltf w θ (t • p) =
      sgn (inner ℝ w p * (t - height w θ p 0)) := by sorry

end QuantumLTF.Membership
