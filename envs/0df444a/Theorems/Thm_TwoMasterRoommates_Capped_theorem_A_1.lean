-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_theorem_A_1
-- name    : TwoMasterRoommates.Capped.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:43:18.887751+00:00
-- url     : https://prove2.me/theorems/cace8ae7-0f28-4737-a2fe-c7aeefa3097e
-- title:
--   Theorem A.1 — marked completion in exponents seven and eight
-- statement:
--   There are two fixed finite programs and absolute constants $D,C,d,c$, with $C>0$, for all finite common-order kernels. For any kernel on $m$ identities and any integer presentation preserving its kinds, marking, weak-rank comparisons and active cap acceptances, the mandatory program correctly decides existence and constructs a witness when there are no optional tokens. The optional program does the same for an arbitrary kernel. Their step bounds are respectively
--
--   $$C(m+1)^7\qquad\text{and}\qquad C(m+1)^8.$$
--
--   Each run uses some $S\le C(m+1)^d$ memory cells, call depth at most $D$, and arithmetic word-formation bound $(m+2)^c$. A zero result asserts nonexistence; a positive result points to an actual matching array. Odd sizes, excess mandatory tokens, zero size, arbitrary caps, and arbitrarily large ties are all included. Both cases are clauses of this one theorem and every constant precedes every instance. This supplies the algorithmic kernel used by the global batch graph.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - reading: rank operations or rank/combinatorial operations → every executed Light step is charged; reason: R1: the stronger reading includes ownership, storage, arithmetic, and reconstruction, as in §B.7
--   - encoding: uniform polynomial time and space in the unit-cost rank model → a fixed Light program, integer comparison presentation, C(n+1)^k time, C(n+1)^d cells, (n+2)^c word-formation bound, and fixed call-depth D; reason: all constants precede all data; raw ranks may be compared or moved without a magnitude restriction; word formation is bounded independently of raw ranks
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 9 (PDF p. 10), Theorem A.1; pp. 11–12 (PDF pp. 12–13), §§A.3–A.4 accounting

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Kernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- Theorem A.1, both mandatory and optional cases, with absolute resource constants. -/
theorem theorem_A_1 :
    ∃ Pm Po : Light.Program, ∃ D C d c : ℕ, 0 < C ∧
      ∀ (m : ℕ) {R : Type} [LinearOrder R] (K : Kernel (Fin m) R)
        (J : Kernel (Fin m) ℤ), KSameComparisons K J →
      (Mandatory K → ∃ S : ℕ, S ≤ C * (m + 1)^d ∧
        Light.Ends ⟨((m + 2)^c : ℤ), S, D⟩ Pm 0 entry (kstart J)
          (C * (m + 1)^7) (KReports K S)) ∧
      (∃ S : ℕ, S ≤ C * (m + 1)^d ∧
        Light.Ends ⟨((m + 2)^c : ℤ), S, D⟩ Po 0 entry (kstart J)
          (C * (m + 1)^8) (KReports K S)) := by sorry

end TwoMasterRoommates.Capped
