-- Prove2me | Theorems.Thm_PersistClust_Count_alive_cell_lift
-- name    : PersistClust.Count.alive_cell_lift
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:48:59.417987+00:00
-- url     : https://prove2.me/theorems/99585eac-a860-4ca3-910c-af6c9fd61e7b
-- title:
--   Alive-up cell lift: below a probe level beta < b, a cell of birth-sup b lifts to a beta-level cell of birth-sup b that descends back onto it
-- statement:
--   Let a 0-dimensional persistence module be given by a filtration law stage/J that is tame, let C_0 be a cell at level s_0 whose birth-sup is b, and let beta be a probe level with s_0 <= beta < b. Then there exists a cell A at level beta such that A has birth-sup exactly b and A coarsens (structMap-descends) down to C_0. The proof: the ancestor-level set of C_0 is nonempty (its own level) and bounded above (tameness: cells are nonempty subsets of their stage, and stages above the tameness ceiling are empty), so its supremum is the birth-sup b; since beta < b, some ancestor level u of C_0 lies above beta, and coarsening that ancestor down to beta exhibits one beta-level cell descending to C_0. Among the finitely many beta-level cells descending to C_0 (the level is finite by tameness), a birth-sup-maximal one is chosen: descent can only weakly increase birth-sup (the rung-B monotonicity), so the chosen cell has birth-sup at least b via the found ancestor pushed to beta; and at most b, since its own descent to s_0 is C_0 whose birth-sup is b. This is the cell lift consumed by the census absorption, the partner construction, and the merge-sync arguments.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the alive-up lift that raises a census cell to a probe level while preserving its birth thread, used by the census absorption, the QSE partner construction and the merge-sync localization. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy; its closure (structMap coarsening composition, identity descent, rung-B birth-sup monotonicity and level bound) is inlined from the same verified lane, and it is the lift inside the accepted census_absorption_mult_nonzero.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem alive_cell_lift {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s₀ b : ℝ} {C₀ : comps stage J s₀}
    (hb : birthSup hLaw s₀ C₀ = b) {β : ℝ} (hs₀β : s₀ ≤ β) (hβb : β < b) :
    ∃ A : comps stage J β, birthSup hLaw β A = b ∧ structMap hLaw hs₀β A = C₀
    := by sorry
