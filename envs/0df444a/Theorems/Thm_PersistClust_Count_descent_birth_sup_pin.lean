-- Prove2me | Theorems.Thm_PersistClust_Count_descent_birth_sup_pin
-- name    : PersistClust.Count.descent_birth_sup_pin
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T19:59:37.670982+00:00
-- url     : https://prove2.me/theorems/b5a8f87b-0d30-406f-8fce-c686e6e9932a
-- title:
--   T5a descent-pin: a pinned alive-up thread keeps birth-sup b at every probe level
-- statement:
--   If a cell C0 at level s0 has birth-sup b, and A is a stage-beta cell with birth-sup b whose descent to s0 is C0 (the alive-up conclusion), then EVERY further descent of A keeps birth-sup exactly b: at any level s <= beta, the descended cell structMap A has birth-sup b. Monotonicity of birth-sup under descent gives both inequalities (down to s and down to s0, where the pinned cell C0 has sup b).
-- source:
--   T5a support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the descent pin that stabilizes the alive-up thread's birth coordinate, consumed by the birth-chain (t5_birthChain) and census arguments of the gate. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem descent_birth_sup_pin {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s₀ b : ℝ} {C₀ : comps stage J s₀} (hb : birthSup hLaw s₀ C₀ = b)
    {β s : ℝ} (hs₀β : s₀ ≤ β) (hβs : s ≤ β) (hs₀s : s₀ ≤ s)
    {A : comps stage J β} (hA : birthSup hLaw β A = b)
    (hP : structMap hLaw hs₀β A = C₀) :
    birthSup hLaw s (structMap hLaw hβs A) = b
    := by sorry
