-- Prove2me | Theorems.Thm_QuantumLTF_Membership_boundarySearchTreeStrict_run
-- name    : QuantumLTF.Membership.boundarySearchTreeStrict_run
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T03:25:29.418712+00:00
-- url     : https://prove2.me/theorems/2fcffd17-5293-4590-9fed-98ca84761ba9
-- title:
--   Correctness of the strict boundary-search query tree
-- statement:
--   If the directional coefficient is nonzero and the threshold height lies in $[-L,L]$, the corrected boundary-search tree returns the true orientation together with exactly the orientation-aware bisection estimate of the height. Its endpoint queries are made strictly outside the promised interval, avoiding ambiguity at zero.
-- source:
--   Supporting lemma for Theorem 3.1 of Fast Quantum Algorithms for Learning Linear Threshold Functions

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTreeStrict
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height

theorem QuantumLTF.Membership.boundarySearchTreeStrict_run {n : ℕ}
    (w p : EuclideanSpace ℝ (Fin n)) (θ L : ℝ) (q : ℕ)
    (ha : inner ℝ w p ≠ 0)
    (hh : |height w θ p 0| ≤ L) :
    (boundarySearchTreeStrict p L q).run (ltf w θ) =
      (sgn (inner ℝ w p),
       orientedBisectValue (sgn (inner ℝ w p)) q (-L) L (height w θ p 0)) := by sorry
