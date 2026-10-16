-- Prove2me | Theorems.Thm_PersistClust_Count_prominent_routing_census
-- name    : PersistClust.Count.prominent_routing_census
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-16T04:35:06.716353+00:00
-- url     : https://prove2.me/theorems/a5b78bd8-bb73-460a-8d20-72c9b45b7ff6
-- title:
--   Routing census of prominent copies: Q^NE-prominent copies of X route to eps-close points of D_Y with fibers bounded by multiplicity
-- statement:
--   Let X and Y be tame 0-dimensional persistence filtrations (FiltrationLaw + IsTameModule) strongly eps-interleaved above alpha (eps >= 0). Then there is a routing P from the prominent off-diagonal copies of X (PromQNE alpha eps) to points of the extended plane such that every routed point has nonzero Y-multiplicity, each copy is routed to a point eps-close to its own point in both coordinates (closeE), and for every point p the number of prominent copies routed to p is at most mult(rank_Y)(p). This is the point-level census form of the prominent sector of the matching of Theorem 4.5.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / 4.8 cluster), from the final closure of the matching gate theorem_4_5_gate_matching (ff828e65, Proved). Mirrors from Def_PersistClust_Count_MatchingCensus / MatchingGate.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem prominent_routing_census {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (hIL : StrongInterleavingAbove stageX JX stageY JY hLawX hLawY α ε hε) :
    ∃ P : {a : offD (mult (rankFn stageX JX)) // PromQNE α ε a} → EReal × EReal,
      (∀ a, mult (rankFn stageY JY) (P a) ≠ 0) ∧
      (∀ a, closeE (offPt a.1).1 (P a).1 ε ∧ closeE (offPt a.1).2 (P a).2 ε) ∧
      (∀ p : EReal × EReal,
        ({a : {a : offD (mult (rankFn stageX JX)) // PromQNE α ε a} | P a = p}).encard
          ≤ mult (rankFn stageY JY) p)
    := by sorry
