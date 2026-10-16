-- Prove2me | Theorems.Thm_PersistClust_Count_qse_demand_injection
-- name    : PersistClust.Count.qse_demand_injection
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-16T04:21:07.632662+00:00
-- url     : https://prove2.me/theorems/2c0bdcc8-d630-4f96-b33a-0d53791bf67d
-- title:
--   Demand injection above a threshold: prominent copies go eps-close in both coordinates, high-far QSE copies birth-close, injectively
-- statement:
--   Let X and Y be tame 0-dimensional persistence filtrations (FiltrationLaw + IsTameModule) that are strongly eps-interleaved above alpha (StrongInterleavingAbove, eps >= 0). Consider the off-diagonal multiplicity copies a of the diagram of X that are demanded (DemandsOff alpha eps a: prominent copies in Q^NE_alpha, i.e. PromQNE, and high-far copies in Q^SE_alpha). Then there is an INJECTIVE map F from the demanded copies of X into the off-diagonal copies of Y such that (1) every PromQNE copy is sent to a copy eps-close in both coordinates (CloseCopy2), and (2) every copy whose point lies in Q^SE_alpha is sent to a copy eps-close in the birth coordinate (CloseCopy1), and eps-close in both coordinates whenever its image lies in Q^NE_alpha. This is one direction of the matching of Theorem 4.5; the other is the same statement with X and Y swapped.
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

theorem qse_demand_injection {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (hIL : StrongInterleavingAbove stageX JX stageY JY hLawX hLawY α ε hε) :
    ∃ F : {a : offD (mult (rankFn stageX JX)) // DemandsOff α ε a}
          → offD (mult (rankFn stageY JY)),
      Function.Injective F ∧
      (∀ a, PromQNE α ε a.1 → CloseCopy2 ε a.1 (F a)) ∧
      (∀ a, offPt a.1 ∈ QSE α → CloseCopy1 ε a.1 (F a) ∧
        (offPt (F a) ∈ QNE α → CloseCopy2 ε a.1 (F a)))
    := by sorry
