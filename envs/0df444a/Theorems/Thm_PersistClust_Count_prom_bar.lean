-- Prove2me | Theorems.Thm_PersistClust_Count_prom_bar
-- name    : PersistClust.Count.prom_bar
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T15:12:27.202833+00:00
-- url     : https://prove2.me/theorems/506147e7-5c42-4716-a572-44f9ba4a4f3d
-- title:
--   Prominent copies sit on real bars (prom-copy to bar extraction)
-- statement:
--   Let a be a prominent copy of the multiplicity diagram mult (rankFn stage J) with prominence level α and diagonal radius ε, i.e. PromQNE α ε a: the offset point offPt a lies in the quadrant Q^NE_α strictly above α in both coordinates, and no diagonal point x is ε-close to offPt a in both coordinates. Then offPt a is a genuine real bar: there exist reals b and d with offPt a = (b, d) and d < b, the bar is wider than the 2ε diagonal band (d + 2ε < b), it lies strictly above the prominence level (α < d), and the multiplicity diagram is nonzero at it (mult (rankFn stage J) (b, d) ≠ 0).
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the prom-copy to bar extraction consumed by the S6 const-squeeze branch of the rank-level kill (t5_l1_rankKill, rankR1) — every prominent copy's offset point is a real, nonzero-multiplicity bar clearing the ε-diagonal band and sitting above the prominence threshold.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem prom_bar {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    {α ε : ℝ} {a : offD (mult (rankFn stage J))} (hprom : PromQNE α ε a) :
    ∃ b d : ℝ, offPt a = ((b : EReal), (d : EReal)) ∧ d < b ∧ d + 2 * ε < b ∧ α < d ∧
      mult (rankFn stage J) ((b : EReal), (d : EReal)) ≠ 0
    := by sorry
