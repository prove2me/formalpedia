-- Prove2me | Theorems.Thm_PersistClust_Count_birth_sup_thread_constancy
-- name    : PersistClust.Count.birth_sup_thread_constancy
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T05:26:25.297209+00:00
-- url     : https://prove2.me/theorems/5c843611-cec3-4718-8dda-a1d165a47a76
-- title:
--   Birth-sup thread constancy across a critical-free window descent
-- statement:
--   Let stage be a cluster filtration over levels ℝ with relation field J satisfying the FiltrationLaw (stage is antitone, J coarsens as the level rises) and IsTameModule (finitely many components per level, no components above a level s₀, and a finite critical set critSet). Write comps stage J t for the component classes at level t, structMap for the coarsening map from level-t classes to level-w classes for w ≤ t, and birthSup hLaw t C for the birth-sup of a class C — the supremum of the levels u ≥ t at which C has an ancestor (structMap hLaw hu C' = C). Theorem: if w ≤ w', the open window is free of critical values (every τ ∈ critSet satisfies τ < w or w' < τ), and the level-w' class C'' descends to the level-w class C (structMap hLaw hww C'' = C), then the birth-sup is constant along the descent thread: birthSup hLaw w C = birthSup hLaw w' C''. Proof: both ancestor-level sets are nonempty (each class is its own ancestor at its own level) and bounded above (tameness: no stage above s₀), so both suprema exist. For the ≤ side, an ancestor level u of C either lies at or below w', in which case the self-ancestor of C'' at w' bounds it, or lies above w'; descending the u-ancestor first to w' gives, by structMap composition, an ancestor of C; injectivity of structMap on the critical-free window (each level-w fiber of the descent is single-valued) forces that descended ancestor to sit in the thread of C'', putting u into the ancestor set of C''. The ≥ side composes any ancestor of C'' at v ≥ w' with the window descent to an ancestor of C. csSup_le / le_csSup assemble both inclusions into the antisymmetric equality.
-- source:
--   T3a thread rung of the persistence-clustering deliverable (RR-6968): birth-sup constancy along the descent thread through a critical-value-free window (t3_bSupThread in the rankKill master, Scratch_rankR1 L769-L824), the engine behind the descent value-constancy lemma (descent_preserves_birth_value) of the T3a value lane.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem birth_sup_thread_constancy {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ)
    {C'' : comps stage J w'} {C : comps stage J w}
    (h : structMap hLaw hww C'' = C) :
    birthSup hLaw w C = birthSup hLaw w' C''
    := by sorry
