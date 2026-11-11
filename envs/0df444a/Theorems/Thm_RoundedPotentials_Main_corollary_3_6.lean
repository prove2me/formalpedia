-- Prove2me | Theorems.Thm_RoundedPotentials_Main_corollary_3_6
-- name    : RoundedPotentials.Main.corollary_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:34:10.857856+00:00
-- url     : https://prove2.me/theorems/43e90814-3d16-4ba2-84a2-006927635c08
-- title:
--   Corollary 3.6 — single-pair completeness
-- statement:
--   For an integer-capacity network with $W\ge1$, distinct terminals $s,t$, and an integer $p\ge0$, suppose $\operatorname{MaxFlow}(s,t)=p$. With $Q_0=32n^2W$, there exist integer indices $i_v$ such that
--   $$0\le i_v\le(2n-1)Q_0,\qquad y_v=i_v/Q_0,$$
--   and $y$ passes all interval, terminal and excess checks (6)–(7). Every index uses at most $3\lfloor\log_2(nW)\rfloor+10$ bits.
--
--   This is the full grid-certificate completeness statement, ready for the concrete integer verifier.
--
--   Differences from the source:
--   - encoding: a finite vertex set V of size n → vertices Fin n and an edge list with distinct loopless ordered pairs; reason: relabeling preserves every flow and cut; m is the actual list length; zero capacities are explicitly allowed in §3
--   - encoding: MaxFlow(s,t) = p → IsGreatest of the set of real values of published IsFlow assignments; reason: records attainment without a real supremum default; the published definition has the same signed conservation equations
--   - reading: O(log(nW)) bits per grid index → binaryDigits ≤ 3 * Nat.log 2 (n * W) + 10; reason: the p.16 bound (2n−1)32n²W < 64(nW)³ implies this uniform explicit bound; one digit encodes zero
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 16, Corollary 3.6; p.17 first line

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Certificate

namespace RoundedPotentials.Main
open scoped BigOperators

theorem corollary_3_6 {n W : ℕ} (I : Instance n W) (hW : 1 ≤ W)
    (s t : Fin n) (hst : s ≠ t) (p : ℤ) (hp : 0 ≤ p) (hmax : MaxValue I s t (p : ℝ)) :
    ∃ i : Fin n → ℤ, IndexRange n W i ∧
      CertificateChecks I n s t p (gridPotential n W i) ∧
      ∀ v, binaryDigits (i v) ≤ 3 * Nat.log 2 (n * W) + 10 := by sorry

end RoundedPotentials.Main
