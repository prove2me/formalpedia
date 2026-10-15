-- Prove2me | Theorems.Thm_ThreeSum_BandEnumeration_candidate_owner
-- name    : ThreeSum.BandEnumeration.candidate_owner
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:12:10.272979+00:00
-- url     : https://prove2.me/theorems/8dd03813-df5c-4caf-ac8f-246a3293748b
-- title:
--   Every relevant band triple is recovered from its selected owner
-- statement:
--   Let $A,B,C$ be finite families of nonempty, ordered, pairwise separated integer intervals, with endpoints $A_i^-,A_i^+$ and similarly for $B,C$. Let $(i,j,k)$ be in-range indices satisfying
--   $A_i^-+B_j^-\le C_k^+$ and $C_k^-\le A_i^++B_j^+$. Select its owner as $BC(j,k)$ if $A_i^-<C_k^--B_j^+$; otherwise choose $AC(i,k)$ when $A_i^-+B_j^-\le C_k^-$ and $AB(i,j)$ in the remaining case. The candidate operation reconstructs the missing index by interval lookup at, respectively, $C_k^--B_j^+$, $C_k^--A_i^-$, or $A_i^-+B_j^-$. Then
--
--   $$
--   \operatorname{candidate}(\operatorname{owner}(i,j,k))
--   =\operatorname{some}(i,j,k).
--   $$
--
--   Thus the quadratic owner catalog includes every relevant triple of bands.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandEnumeration.lean#L77-L99

import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_BinarySearch_locate_complete


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandEnumeration.Family
end ThreeSum.BandEnumeration.Family

theorem ThreeSum.BandEnumeration.candidate_owner : ∀ (A B C : ThreeSum.BandEnumeration.Family) (t : ThreeSum.BandEnumeration.Triple A B C)
  (ht : ThreeSum.BandEnumeration.relevant A B C t),
  @Eq.{1} (Option.{0} (ThreeSum.BandEnumeration.Triple A B C))
    (ThreeSum.BandEnumeration.candidate A B C (ThreeSum.BandEnumeration.owner A B C t))
    (@Option.some.{0} (ThreeSum.BandEnumeration.Triple A B C) t) := by
  sorry
