-- Prove2me | Theorems.Thm_PersistClust_Count_band_census_transfer_ge
-- name    : PersistClust.Count.band_census_transfer_ge
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T08:15:08.320288+00:00
-- url     : https://prove2.me/theorems/6a2e02de-8b58-4b5f-aa98-16d01b6f7059
-- title:
--   Band-census transfer: the b-census of X at the census level injects into the b-band census of Y at every probe level
-- statement:
--   Two tame persistence modules are related by level-shifting maps φ (X to Y, level β to β−ε) and ψ (Y to X, likewise) obeying the naturality squares including the round-trip square. Fix b, d, η₀, δx with η₀ < δx and d+η₀+2ε < b, α < d, and assume every critical level τ ≠ d of X is at distance greater than δx from d. Then for every probe level β with d+2ε < β ≤ d+η₀+2ε such that Y has at least one component class at level β−ε, the number (encard) of X-component classes at level d+η₀ with birth-supremum exactly b is at most the number of Y-component classes at level β−ε whose birth-supremum lies in the band [b−ε, b+ε].
-- source:
--   Rung-F' of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the rank-level band-count lower bound. At every probe source level β ∈ (d+2ε, d+η₀+2ε], the b-band census of Y at level β−ε dominates the b-census of X at level d+η₀: the φ-images of the aliveUp-lifts are pairwise-distinct b-band cells (the image-thread band pin), with ψ-pullbacks the descents of distinct census cells — distinct by crit-injectivity on the crit-free window [β−2ε, d+η₀] (X-gap at d). This is the (A)-case seed and the (B)-case counted-X exhibit of the rank-level kill (design §8.15).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem band_census_transfer_ge {ιX ιY : Type*}
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
    (hNE : Nonempty (comps stageY JY (β - ε)))
    (hβlo : d + 2 * ε < β) (hβhi : β ≤ d + η₀ + 2 * ε) :
    ({C : comps stageX JX (d + η₀) | birthSup hLawX (d + η₀) C = b} :
        Set (comps stageX JX (d + η₀))).encard ≤
    ({I : comps stageY JY (β - ε) | b - ε ≤ birthSup hLawY (β - ε) I ∧
        birthSup hLawY (β - ε) I ≤ b + ε} : Set (comps stageY JY (β - ε))).encard
    := by sorry
