-- Prove2me | Theorems.Thm_PersistClust_Count_noncritical_level_mult_zero
-- name    : PersistClust.Count.noncritical_level_mult_zero
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:16:37.146145+00:00
-- url     : https://prove2.me/theorems/b39ee7f7-ba9d-437e-9f5b-94630b757168
-- title:
--   No essential bar is born at a non-critical level: mult(rankFn)(b, ⊥) = 0
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. If b is a real level outside the critical set (hb : b ∉ (critSet hTame : Set ℝ)), then the multiplicity of the vertical bar born at b is zero: mult (rankFn stage J) ((b : EReal), (⊥ : EReal)) = 0. Proof sketch: the multiplicity at (b, ⊥) is the infimum over ε > 0 and t ≤ b − ε of the difference rankFn (b − ε) t − rankFn (b + ε) t; since every cell's birth-supremum lies in the critical set, a δ₀-gap around b excludes all birth-sups from the window (b − δ₀/2, b + δ₀/2), so at t = b − 1 the window-split rank identity gives rankFn (b − δ₀/2) (b − 1) − rankFn (b + δ₀/2) (b − 1) = encard of the empty set = 0 (using the ℕ∞ subtraction cancellation with the finiteness of the ranks from q-tameness); the infimum over all (ε, t) is then ≤ 0, and being an encard difference it is ≥ 0, hence 0. Birth levels of essential bars are therefore always critical.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): T3a-ii(c) (t3_ess_pin in the rankKill master, Scratch_rankR1 L1998-2047) with its full inlined helper chain — structMap_comp L77-95, t3_fresh_in_critSet L400-453, t3_rank_meets L468-490, t3_structMap_id L493-496, t3_desc_point L500-521, t3_meets_birthSup L525-576, t3_rank_orig L581-589, t2_qtame L595-609, t3_windowEx L635-690, t3_ancSup_mem L694-740, t3_birthSup_in_critSet L825-861, t3_windowSplit L865-890, t3_add_sub L893-899, t3_gapEx L956-977, t3_bSup_self_crit L1030-1048, t3_bSup_in_crit L1052-1057 — the bar-birth pin of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem noncritical_level_mult_zero {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b : ℝ}
    (hb : b ∉ (critSet hTame : Set ℝ)) :
    mult (rankFn stage J) ((b : EReal), (⊥ : EReal)) = 0
    := by sorry
