-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_partition_tag_weight_encoding
-- name    : TwoAgentSched.TotalTotal.partition_tag_weight_encoding
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:11:36.369731+00:00
-- url     : https://prove2.me/theorems/779cd343-393f-4afa-8b7e-2b1ae9d2abbe
-- title:
--   Canonical binary code of a tagged PARTITION gadget weight
-- statement:
--   For nonnegative integers $i,d$ and a positive integer $m$, let $\operatorname{enc}(m)$ denote its canonical least-significant-bit-first binary code followed by a separator. Then
--
--   $$
--   \operatorname{enc}\!\left(2(4^{i+d+1}m+4^i)\right)
--    = 0^{2i+1}\,1\,0^{2d+1}\operatorname{enc}(m).
--   $$
--
--   This gives the exact binary form of the positive-weight member of the distinct-even PARTITION gadget used to support the corrected scheduling reduction. The tagging gadget is an additional construction; this code identity is not stated in the cited paper. It supplies a transducer specification, but is not itself a polynomial-time computation claim.
-- source:
--   Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2 and proof, pp. 237–238. Binary code identity for the additional distinct-even PARTITION tagging gadget.

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace TwoAgentSched.TotalTotal

open ProjSchedTW.Complexity

theorem partition_tag_weight_encoding (i d m : ℕ) (hm : 0 < m) :
    encNat (2 * (4 ^ (i + d + 1) * m + 4 ^ i)) =
      List.replicate (2 * i + 1) BSym.zero ++ BSym.one ::
        (List.replicate (2 * d + 1) BSym.zero ++ encNat m) := by sorry

end TwoAgentSched.TotalTotal
