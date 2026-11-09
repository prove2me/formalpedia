-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_terminal_8
-- name    : TwoMasterRoommates.Capped.terminal_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:43:09.605208+00:00
-- url     : https://prove2.me/theorems/6fef4ea4-f4ff-49cb-bd35-30068eda7a5b
-- title:
--   §B.1 Eq. (8) — at most two internal entering targets
-- statement:
--   Let $M$ be a capped stable matching in the per-tier normal form of Lemma B.2. For arbitrary cuts $t,j$, put $L_A=\{v\in A:a(v)=t,b(v)>j\}$. Count the identities in $L_A$ whose mate is in $A$ and either has $a$ rank below $t$, or has $a$ rank $t$ and $b$ rank at most $j$. Then
--
--   $$\bigl|\{v\in L_A: Mv\in A,\ a(Mv)<t\ \text{or}\ (a(Mv)=t\text{ and }b(Mv)\le j)\}\bigr|\le2.$$
--
--   The observer-class condition applies to both alternatives. The conclusion is for every cut, including cuts not selected by a scan. It retains the two permitted entering targets; arbitrary caps do not justify replacing two by one. This is the deletion-label bound required by the batch interface.
--
--   Differences from the source:
--   - generalization: real-valued weak ranks → ranks in any linear order; reason: finite attained values and their comparisons embed in the real source domain; specialize the rank type to the reals
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 13 (PDF p. 14), §B.1 equation (8) and the immediately following bound

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_NormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- §B.1, equation (8): two entering internal targets, at every cut. -/
theorem terminal_8 {R : Type} [LinearOrder R] {n : ℕ} (I : Instance R n)
    (M : Fin n → Fin n) (hM : IsSolution I M) (hN : NormalForm I M) (t j : R) :
    (enteringTargets I M t j).card ≤ 2 := by sorry

end TwoMasterRoommates.Capped
