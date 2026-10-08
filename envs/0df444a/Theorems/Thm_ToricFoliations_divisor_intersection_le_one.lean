-- Prove2me | Theorems.Thm_ToricFoliations_divisor_intersection_le_one
-- name    : ToricFoliations.divisor_intersection_le_one
-- status  : Open
-- author  : @hiraeth
-- created : 2026-10-07T12:31:04.931907+00:00
-- url     : https://prove2.me/theorems/73d57787-7702-48a9-a6a1-8cd6224823d6
-- title:
--   $D\cdot C\le 1$ for every torus-invariant divisor along a wall curve
-- statement:
--   **theorem_title:** $D\cdot C\le 1$ for every torus-invariant divisor along a wall curve
--
--   Let $X$ be a projective $\mathbb Q$-factorial toric variety, and let
--   $C=V(W)$ be a torus-invariant curve corresponding to the wall
--   $W=\langle v_1,\dots,v_{n-1}\rangle$ of the fan. Let
--   $v_n,v_{n+1}$ be the primitive vectors completing the two maximal cones
--   $\sigma,\sigma'$ adjacent to $W$, and let $a_1,\dots,a_{n+1}$ be the integers
--   of the wall relation (3.1), normalized by
--   $\gcd(a_1,\dots,a_{n+1})=1$, ordered
--   $a_1\le\cdots\le a_n\le a_{n+1}$ with $a_n,a_{n+1}>0$, and with the
--   multiplicity divisibility
--   $\mathrm{mult}(W)\mid\mathrm{mult}(\sigma),\mathrm{mult}(\sigma')$.
--
--   Then for every index $i$, the intersection number of the torus-invariant
--   prime divisor $D_{v_i}=V(\langle v_i\rangle)$ with $C$ satisfies
--
--   $$
--   D_{v_i}\cdot C\le 1.
--   $$
--
--   This is the estimate used immediately after equation (3.2) in the proof of
--   Theorem 1.3; together with the pigeonhole step it produces at least $r+1$
--   vectors of the wall lying in $V$.
--
--   **Formalization Note.** The theorem asserts `divisorIntersection C i ≤ 1` for
--   every `i : Fin (n+1)`, where all hypotheses are fields of `WallData n`.
-- source:
--   Fujino--Sato 2024, A remark on toric foliations, Arch. Math. 122 (2024) 621--627, https://doi.org/10.1007/s00013-024-01991-1 (arXiv:2309.09461), Section 3, after eq. (3.2)

import Mathlib
import Definitions.Def_ToricFoliations

open scoped BigOperators

namespace ToricFoliations

/--
Equation (3.1) plus the sorted relation (3.2) and the multiplicity
divisibility from the fan imply `D . C <= 1` for every torus-invariant prime
divisor `D` on `X`.  This is the step right after (3.2) in the proof of
Theorem 1.3.
-/
theorem divisor_intersection_le_one {n : ℕ} (C : WallData n) :
    ∀ i : Fin (n + 1), divisorIntersection C i ≤ 1 := by
  sorry

end ToricFoliations
