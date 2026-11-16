-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_Supplement_lemma_C_4
-- name    : TwoMasterRoommates.Capped.Supplement.lemma_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:34:50.793423+00:00
-- url     : https://prove2.me/theorems/a64b4ceb-9fb6-48b0-bf64-ec82f9375380
-- title:
--   Lemma C.4 — future signatures are constant on a local bucket
-- statement:
--   In a one-master-plus-outliers instance, let $o$ be an outlier and $B_o$ a local bucket of $o$ (§C.1: a nonempty intersection of a cell of the critical set $C_o$ with the local qualities $\Lambda_o$, further cut to $(-\infty,\theta_o]$ when $|F_o^+|\ge s+2$). Let $a$ be either an outlier other than $o$ or a follower with $\rho(a)>\rho(o)$. Then for all $q,q'\in B_o$
--
--   $$r_o(a)<q\iff r_o(a)<q'.$$
--
--   So the strict-desire indicator of a local outlier towards other outliers and later followers depends only on its bucket, which is what lets Theorem C.1's dynamic program forget the exact local quality.
--
--   Differences from the source:
--   - encoding: complete weak orders (the master ρ and the outlier rows) → integer rank functions, smaller is better, equal values tied; reason: every weak order on a finite set is represented by integer ranks and only comparisons are used (§3)
--   - encoding: the singleton critical values and the open intervals between consecutive critical values, including the two end intervals → a singleton {c} with c ∈ C_o, or an open interval whose ends are critical values or ±∞ and which contains no critical value; reason: an interval with critical or infinite ends and no critical value inside has consecutive ends; one with ends out of order is empty and gives no bucket
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 19 (PDF p. 20), Lemma C.4 and the bucket construction before it

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Supplement_OneMaster

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

/-- Lemma C.4 (future signatures), Bin Yu, STOC 2027 submission #225, p. 19 (PDF 20): for a
local bucket `B_o`, the truth of `r_o(a) < q` is the same for all `q ∈ B_o` whenever `a` is
another outlier or a follower strictly later than `o` in the master. -/
theorem lemma_C_4 {N : ℕ} (I : OneMasterInstance N) (o : Fin N) (ho : I.isOut o = true)
    (B : Set ℤ) (hB : I.IsLocalBucket o B) (a : Fin N)
    (ha : (I.isOut a = true ∧ a ≠ o) ∨ (I.isOut a = false ∧ I.ρ o < I.ρ a))
    (q q' : ℤ) (hq : q ∈ B) (hq' : q' ∈ B) :
    I.row o a < q ↔ I.row o a < q' := by sorry

end TwoMasterRoommates.Capped.Supplement
