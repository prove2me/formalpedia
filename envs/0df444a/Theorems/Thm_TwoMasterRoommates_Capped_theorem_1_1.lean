-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_theorem_1_1
-- name    : TwoMasterRoommates.Capped.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:38:18.831304+00:00
-- url     : https://prove2.me/theorems/1553a9b3-2467-418b-aaf4-e90028698d86
-- title:
--   Theorem 1.1 (= B.1) — capped weakly stable perfect matching in polynomial time
-- statement:
--   There is one fixed finite program $P$ and absolute constants $D,C,d,c$, with $C>0$, for all two-master instances $I$ on $n$ identities. Ranks may have arbitrary ties, observer classes may be empty, and personal upper caps are unrestricted. On any integer presentation $J$ preserving the two original weak master orders and every cap acceptance, the program terminates within
--
--   $$C(n+1)^{31}\text{ steps},\qquad S\le C(n+1)^d\text{ memory cells}.$$
--
--   It either reports correctly that no capped weakly stable perfect matching of $I$ exists, or returns an actual such matching in memory. All blocking comparisons are the two original strict inequalities. Both branches refer to the unrefined instance, so the negative branch excludes every original weakly stable cap-feasible perfect matching. The arithmetic word-formation limit is $(n+2)^c$ and call depth is at most $D$, independently of rank magnitude. The empty population has its empty matching; odd sizes must be rejected correctly.
--
--   The same program works for every linear-order rank type through its integer comparison presentation. Every instance has such a presentation by cap compression. The constant and all resource exponents precede all types and data. This is the full decision-and-construction theorem, including polynomial space and exponent 31.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - reading: rank operations or rank/combinatorial operations → every executed Light step is charged; reason: R1: the stronger reading includes ownership, storage, arithmetic, and reconstruction, as in §B.7
--   - reading: no input preference tie is refined → both output branches are correct for the original weak instance; reason: R2: strict mutual improvement tests original ranks; nonexistence excludes every matching of the unrefined instance
--   - encoding: uniform polynomial time and space in the unit-cost rank model → a fixed Light program, integer comparison presentation, C(n+1)^k time, C(n+1)^d cells, (n+2)^c word-formation bound, and fixed call-depth D; reason: all constants precede all data; raw ranks may be compared or moved without a magnitude restriction; word formation is bounded independently of raw ranks
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 1 (PDF p. 2), Theorem 1.1; p. 12 (PDF p. 13), Theorem B.1; pp. 17–18 (PDF pp. 18–19), §B.7

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Encoding

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- Theorem 1.1 (= B.1), one uniform program, decision and construction, all original ties. -/
theorem theorem_1_1 :
    ∃ P : Light.Program, ∃ D C d c : ℕ, 0 < C ∧
      ∀ (n : ℕ) {R : Type} [LinearOrder R] (I : Instance R n)
        (J : Instance ℤ n), SameComparisons I J →
      ∃ S : ℕ, S ≤ C * (n + 1)^d ∧
        Light.Ends ⟨((n + 2)^c : ℤ), S, D⟩ P 0 entry (start J)
          (C * (n + 1)^31) (Reports I S) := by sorry

end TwoMasterRoommates.Capped
