-- Prove2me | Theorems.Thm_ThreeSum1960614_local_cover_bounds
-- name    : ThreeSum1960614.local_cover_bounds
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:09:00.418115+00:00
-- url     : https://prove2.me/theorems/76a91726-7da4-44a8-9973-ec007a038c4c
-- title:
--   Local-cover incidence and degree bounds for general expansion
-- statement:
--   For natural $c\ge3$ and $h>0$, set $s=2h$, $L=cs$, $M=\binom Ls$, $V=\binom Lh$, $\Delta=\binom{L-h}h$, and $G=\binom sh$. Then $V\Delta=MG$, $\Delta\le V$, $G<2^s<M$, and $\Delta^2<M2^s$. This finite statement permits expansion 232; it does not by itself establish the global encoding or machine cost.
-- source:
--   User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md (14 October 2026); Section 6; upstream https://github.com/c0ldzy17/three-sum-lean/tree/2b639655e07421b9ac743de9090459bab473a7c0

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.local_cover_bounds (c h : ℕ)
    (hc : 3 ≤ c) (hh : 0 < h) :
    Nat.choose (c * (2 * h)) h * Nat.choose (c * (2 * h) - h) h =
      Nat.choose (c * (2 * h)) (2 * h) * Nat.choose (2 * h) h ∧
    Nat.choose (c * (2 * h) - h) h ≤ Nat.choose (c * (2 * h)) h ∧
    Nat.choose (2 * h) h < 2 ^ (2 * h) ∧
    2 ^ (2 * h) < Nat.choose (c * (2 * h)) (2 * h) ∧
    Nat.choose (c * (2 * h) - h) h ^ 2 <
      Nat.choose (c * (2 * h)) (2 * h) * 2 ^ (2 * h) := by sorry
