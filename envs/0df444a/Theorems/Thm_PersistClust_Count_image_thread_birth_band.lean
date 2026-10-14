-- Prove2me | Theorems.Thm_PersistClust_Count_image_thread_birth_band
-- name    : PersistClust.Count.image_thread_birth_band
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T08:12:45.757868+00:00
-- url     : https://prove2.me/theorems/29c98755-f57a-4d18-926b-7fd9af53f59d
-- title:
--   Image-thread birth band at every probe level (φ-image of an aliveUp-lift is a b-band cell)
-- statement:
--   Two tame persistence modules are related by level-shifting maps φ (from X, shifting a level β to β−ε) and ψ (from Y, likewise) obeying the natural naturality squares with respect to the structure maps, including the round-trip square making ψ of an image equal to a further descent of the source. Let C be a component class of X at level d+η₀ with birth-supremum exactly b, where b is strictly above d+η₀+2ε. Assume the parameter level β lies in the band (d+2ε, d+η₀+2ε], that α < d, that η₀ < δx, and that every critical level τ ≠ d of X is at distance greater than δx from d. Then there exists a component class I of Y at level β−ε whose birth-supremum lies in the band [b−ε, b+ε], and whose ψ-pullback at level β−ε is exactly the descent of C from level d+η₀ to level β−2ε.
-- source:
--   Rung-F seed of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the φ-image of an X census cell's aliveUp-lift is a b-band Y-cell at EVERY probe source level β ∈ (d+2ε, d+η₀+2ε], with its ψ-pullback pinned to the census cell's descent at level β−2ε (design §8.15). The source is the d+η₀+2ε aliveUp-lift descended to β, so the image-birth-upper pin reads the double-descent at β−2ε ∈ (d, d+η₀], where the crit-free window from the δx gap at d keeps the birth exactly b. This is the level-parameterized form of the deathBar pins (4)–(5) and the injection seed of the rank-level kill.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem image_thread_birth_band {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d η₀ δx β : ℝ}
    (hη₀δx : η₀ < δx)
    (hgapd : ∀ τ ∈ critSet hTameX, τ ≠ d → δx < |τ - d|)
    (hlim : d + η₀ + 2 * ε < b)
    (hαd : α < d)
    (hβlo : d + 2 * ε < β) (hβhi : β ≤ d + η₀ + 2 * ε)
    (C : comps stageX JX (d + η₀)) (hbC : birthSup hLawX (d + η₀) C = b) :
    ∃ I : comps stageY JY (β - ε),
      b - ε ≤ birthSup hLawY (β - ε) I ∧
      birthSup hLawY (β - ε) I ≤ b + ε ∧
      ψ (β - ε) (show α ≤ β - ε by linarith) I =
        structMap hLawX (show β - ε - ε ≤ d + η₀ by linarith) C
    := by sorry
