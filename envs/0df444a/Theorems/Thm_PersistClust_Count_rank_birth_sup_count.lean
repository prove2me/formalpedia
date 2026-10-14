-- Prove2me | Theorems.Thm_PersistClust_Count_rank_birth_sup_count
-- name    : PersistClust.Count.rank_birth_sup_count
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T08:57:15.667974+00:00
-- url     : https://prove2.me/theorems/39cc1a23-1ca8-4402-8b00-7f752d704fac
-- title:
--   Rank identity in birth-sup form: r(s,t) counts the cells whose birth-sup exceeds s
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. For real levels t ≤ s such that s differs from the birth-supremum of every t-cell (hs : ∀ C : comps stage J t, s ≠ birthSup hLaw t C), the rank function satisfies rankFn stage J s t = {C : comps stage J t | s < birthSup hLaw t C}.encard: the rank of (s,t) — the extended cardinality of the family of t-classes of points alive at s — equals the number of t-cells whose birth-supremum strictly exceeds s. Proof: the rank unfolds (t3_rank_meets) to the encard of the image of stage s under x ↦ {y | J t x y}, and that image is exactly the Subtype.val image of the t-cells meeting stage s (each such class is a component at t since stage is antitone), with encard preserved by injectivity; then cell-wise (t3_meets_birthSup, via t3_structMap_id and t3_desc_point) a t-cell meets stage s iff s is strictly below its birth-supremum — the ancestor level set AncSet is nonempty (contains t by structMap identity) and bounded (tameness volume axiom), its supremum is the birth-sup, membership pushes s ≤ birthSup with equality excluded by hs, and conversely s < birthSup produces an ancestor level u > s whose representative point descends to stage s with t-class C.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the birth-SUP form of the T3 rank identity (t3_rank_orig in the rankKill master, Scratch_rankR1 L581-589, with inlined helpers t3_rank_meets L468-490, t3_structMap_id L493-496, t3_desc_point L500-521, t3_meets_birthSup L525-576) — the generic rank form consumed by the window-split, box arithmetic and combination machinery of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem rank_birth_sup_count {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s t : ℝ} (hst : t ≤ s)
    (hs : ∀ C : comps stage J t, s ≠ birthSup hLaw t C) :
    rankFn stage J s t = {C : comps stage J t | s < birthSup hLaw t C}.encard
    := by sorry
