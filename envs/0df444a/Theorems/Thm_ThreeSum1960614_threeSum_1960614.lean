-- Prove2me | Theorems.Thm_ThreeSum1960614_threeSum_1960614
-- name    : ThreeSum1960614.threeSum_1960614
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:10:16.03444+00:00
-- url     : https://prove2.me/theorems/a53b364e-57a0-4d2c-adc6-983a74218a4b
-- title:
--   3SUM in O(n^1.960614) word-RAM steps
-- statement:
--   For every fixed natural integer-size exponent $\kappa$, there exist a finite deterministic word-RAM program $P$, a natural word-width constant $b$, and a natural-valued time function $T$. For every input size $n$, every list of $n$ integers of absolute value at most $n^\kappa$, and every word width $W\ge b(\lfloor\log_2n\rfloor+1)$, the program halts within $T(n)$ steps and accepts exactly when three pairwise distinct positions sum to zero. Repeated values at different positions are allowed. For the reduced rational $1.960614=980307/500000$, there is a natural $K$ such that $T(n)^{500000}\le K n^{980307}$ for every $n\ge2$. This exact campaign goal remains unproved until the modified complete program and runtime bridge are closed; it is not asserted to follow from numeric checks alone.
-- source:
--   User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md (14 October 2026); Section 0: intended machine target; upstream https://github.com/c0ldzy17/three-sum-lean/tree/2b639655e07421b9ac743de9090459bab473a7c0

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.threeSum_1960614 :
    EndStatement.ThreeSum.SolvedInTime 1.960614 := by sorry
