-- Prove2me | Theorems.Thm_ThreeSum_BandEnumeration_Family_lookup_sound
-- name    : ThreeSum.BandEnumeration.Family.lookup_sound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:11:46.400984+00:00
-- url     : https://prove2.me/theorems/a280b5aa-bb03-407d-aebf-cf66805a4991
-- title:
--   Successful interval lookup returns a containing band
-- statement:
--   Let $A$ be a finite family of integer intervals $[\ell_i,u_i]$, indexed by $0\le i<N$. Assume each interval is nonempty, the lower endpoints are nondecreasing, and $u_i<\ell_j$ whenever $i<j<N$. For $x\in\mathbb Z$ and an in-range index $i$, if the family's binary-search lookup returns $i$, then
--
--   $$
--   \operatorname{lookup}_A(x)=\operatorname{some}(i)
--   \quad\Longrightarrow\quad \ell_i\le x\le u_i.
--   $$
--
--   The lookup includes a check that its returned index lies in the family.
--
--   This supplies the interval-containment guarantee for successful band-candidate lookups.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandEnumeration.lean#L41-L53

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
import Theorems.Thm_ThreeSum_BinarySearch_locate_sound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandEnumeration.Family
end ThreeSum.BandEnumeration.Family

theorem ThreeSum.BandEnumeration.Family.lookup_sound : ∀ (A : ThreeSum.BandEnumeration.Family) (x : Int) (i : A.Index)
  (h : @Eq.{1} (Option.{0} A.Index) (A.lookup x) (@Option.some.{0} A.Index i)),
  And (@LE.le.{0} Int Int.instLEInt (A.lo i) x) (@LE.le.{0} Int Int.instLEInt x (A.hi i)) := by
  sorry
