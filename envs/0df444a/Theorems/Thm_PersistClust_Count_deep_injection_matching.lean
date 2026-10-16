-- Prove2me | Theorems.Thm_PersistClust_Count_deep_injection_matching
-- name    : PersistClust.Count.deep_injection_matching
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T21:43:08.70755+00:00
-- url     : https://prove2.me/theorems/24c85ba0-a794-4bee-8d34-3bd151134134
-- title:
--   Induced-matching stability above a threshold: interleaved tame 0-dim filtrations admit an eps-close injection on all bars with margins
-- statement:
--   Let X and Y be tame 0-dimensional persistence filtrations (FiltrationLaw + IsTameModule) that are strongly eps-interleaved above alpha (StrongInterleavingAbove). Fix kappa > 0. Then the multiplicity copies of X at real bars (b, d) with margins alpha + kappa <= d and d + 2 eps + kappa <= b admit an INJECTIVE map F into the multiplicity copies of Y such that every copy is sent to a copy eps-close in both coordinates (closeE in birth and in death). This is the hard direction of algebraic stability (the matching), localized above the threshold, for bars bounded away from alpha and from the diagonal.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / 4.8 cluster): the generalized box lemma for overlapping eps-boxes, proved via the Bauer-Lesnick induced matching (Induced Matchings and the Algebraic Stability of Persistence Barcodes) adapted to component filtrations. It closes the census atoms of the deliverable's matching gate (the demand routing and the rank-kill leaf). Mirrors from Def_PersistClust_Count_MatchingCensus.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem deep_injection_matching {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (hε : 0 ≤ ε) (hIL : StrongInterleavingAbove stageX JX stageY JY hLawX hLawY α ε hε)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ F : {x : offD (mult (rankFn stageX JX)) // ∃ b d : ℝ,
        offPt x = (((b : ℝ) : EReal), ((d : ℝ) : EReal)) ∧ α + κ ≤ d ∧ d + 2 * ε + κ ≤ b} →
        offD (mult (rankFn stageY JY)),
      Function.Injective F ∧ ∀ x, closeE (offPt x.1).1 (offPt (F x)).1 ε ∧
        closeE (offPt x.1).2 (offPt (F x)).2 ε
    := by sorry
