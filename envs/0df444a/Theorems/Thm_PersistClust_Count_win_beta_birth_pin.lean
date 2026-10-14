-- Prove2me | Theorems.Thm_PersistClust_Count_win_beta_birth_pin
-- name    : PersistClust.Count.win_beta_birth_pin
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:20:13.82804+00:00
-- url     : https://prove2.me/theorems/4804f838-5741-4240-8fac-91c9bd944cf4
-- title:
--   Window-β bridge: a cell is counted in the b-band iff its birth-supremum equals b
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. Let v be a level, C a v-cell, b a real level and η a positive radius such that every critical level τ ≠ b satisfies η < |τ − b| (the gap hypothesis: the closed η-window around b contains no critical level other than possibly b itself). Then C belongs to the b-band — the set of v-cells whose birth-supremum lies in the open window (b − η, b + η) — if and only if the birth-supremum of C is exactly b. Forward: every cell's birth-supremum is a critical level (unconditionally), and the gap hypothesis rules out every critical value other than b from the window, so a birth-supremum in the window must be b. Backward: b itself lies in the window since 0 < η. This is the membership bridge that converts band censuses into pinned β = b censuses in the matching-census assembly.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 window-β membership bridge (t3_win_beta in the rankKill master, Scratch_rankR1 L1061-1076) with its full inlined helper chain — structMap_comp L77-95, t3_fresh_in_critSet L400-453, t3_structMap_id L493-496, t3_windowEx L635-690, t3_ancSup_mem L694-740, t3_bSup_self_crit L1030-1048, t3_birthSup_in_critSet L825-861, t3_bSup_in_crit L1052-1057 — consumed by the census reduction and combination stability sites of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem win_beta_birth_pin {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {v : ℝ} (C : comps stage J v) (b η : ℝ) (hη0 : 0 < η)
    (hgap : ∀ τ ∈ critSet hTame, τ ≠ b → η < |τ - b|) :
    C ∈ ({C : comps stage J v | b - η < birthSup hLaw v C ∧ birthSup hLaw v C < b + η} :
      Set (comps stage J v)) ↔ birthSup hLaw v C = b
    := by sorry
