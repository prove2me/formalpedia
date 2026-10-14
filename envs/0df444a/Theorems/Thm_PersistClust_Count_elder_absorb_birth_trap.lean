-- Prove2me | Theorems.Thm_PersistClust_Count_elder_absorb_birth_trap
-- name    : PersistClust.Count.elder_absorb_birth_trap
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T08:26:02.099334+00:00
-- url     : https://prove2.me/theorems/30860720-9eab-4a42-96fe-9c78542926b3
-- title:
--   Elder trap: the Y-descent of an image thread is birth-capped by the source thread's birth plus ε
-- statement:
--   Let X and Y be tame persistence modules related by level-shifting maps φ (X to Y, level β to β−ε) and ψ (Y to X, likewise) obeying the naturality squares (ii') and (iv'), the latter being the round-trip square identifying ψ of an image with a further descent of the source. Take an X-class A at level β (with α ≤ β and α ≤ β−ε) with birth-supremum b, which descends onto a census pin C₀ at level s₀ ≤ β also having birth-supremum b. Let d be a level with d+2ε < β and let v be a probe level with d+ε < v ≤ β−ε (and the level conditions s₀ ≤ v−ε, α ≤ v, α ≤ v−ε). If the descent of the image φ_β(A), taken to the level v, has birth-supremum b3, then b3 ≤ b + ε: an absorbing elder image thread is trapped by the source thread's birth band.
-- source:
--   Elder-trap of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): absorbing elders are birth-trapped. The identity (a) composes the two squares so that ψ pulls the Y-descent of the image back onto the X-descent of A at v−ε; the X-thread pin (hDescPin: value exactly b at every level of the descent ray above the census anchor) then caps every ancestor of the Y-descent: each ancestor u pulls back to an ancestor of the X-descent at u−ε ≤ b, and the supremum over ancestors is at most b+ε. Consumed by the full-cap and rank-kill branches (design part 4, §8.12/§8.15).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem elder_absorb_birth_trap {ιX ιY : Type*} {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d β : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε)
    {A : comps stageX JX β} (hA : birthSup hLawX β A = b)
    {s₀ : ℝ} {C₀ : comps stageX JX s₀} (hbC₀ : birthSup hLawX s₀ C₀ = b)
    (hs₀β : s₀ ≤ β) (hP : structMap hLawX hs₀β A = C₀)
    (hd : d + 2 * ε < β) {v : ℝ} (hv : d + ε < v) (hvE : v ≤ β - ε)
    (hvα : α ≤ v) (hvεα : α ≤ v - ε) (hs₀v : s₀ ≤ v - ε)
    {b3 : ℝ} (hM : birthSup hLawY v (structMap hLawY (show v ≤ β - ε by linarith)
        (φ β hβ A)) = b3) :
    b3 ≤ b + ε
    := by sorry
