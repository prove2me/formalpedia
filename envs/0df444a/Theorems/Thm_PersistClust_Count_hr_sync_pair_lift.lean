-- Prove2me | Theorems.Thm_PersistClust_Count_hr_sync_pair_lift
-- name    : PersistClust.Count.hr_sync_pair_lift
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T15:16:36.932491+00:00
-- url     : https://prove2.me/theorems/d0506d75-633c-4804-8692-6739d4abed08
-- title:
--   Sync-pair core at the canonical probe: a bar of X lifts to a carrier/elder pair, alive-up lifts, an image birth band [b − ε, b + ε], distinct images, and a co-merged image thread by d − η₀ − ε
-- statement:
--   Let X and Y be two tame filtration modules connected by an ε-interleaving pair: φ maps X-cells at level β ≥ α to Y-cells at β − ε, ψ maps back the same way, and the naturality squares hSq1, hSq2 hold (φ and ψ commute with the level-descent maps structMap) together with the pullback round-trip square hSq4 (descending φβ(x) back through ψ gives the original descent). For a bar (b, d) of X with d < b whose multiplicity mult (rankFn) ((b, d)) is nonzero, with the critical levels δx-far from b and from d, a pin offset η₀ with 0 < η₀ < δx below half the bar width, the bar-separation slack η₀ < b − d − 2ε (so the probe β := d + η₀ + 2ε stays below b), and the α-slack η₀ < d − α: at the canonical probe β the theorem delivers (i) the carrier/elder pair — two DISTINCT cells C₁, C₂ at level d + η₀ with birthSup C₁ = b, b ≤ birthSup C₂, whose descents to d − η₀ coincide (the carrier-elder pigeonhole); (ii) their alive-up lifts A₁, A₂ at β with birthSup A₁ = b, birthSup A₂ = birthSup C₂, descending back to C₁ and C₂; (iii) the carrier image I₁ = φ_β A₁ whose Y-birth-supremum at the image level β − ε lies in the band [b − ε, b + ε]; (iv) DISTINCT image cells I₁ ≠ I₂ = φ_β A₂; and (v) the image co-merge: the two φ-images descend to the SAME Y-cell by the level d − η₀ − ε (the merge level d − η₀ in place of d, per the carrier-elder change note). This is the per-copy sync-pair core of the hr route step (3): the packaged input for the merge-level extraction m′ and the value cases at (b₂, m′) in the matching-census fiber count.
-- source:
--   Support tool of the persistence-clustering deliverable (hr-route step 3 satellite, carrierE2 fill, rankKill master Scratch_rankR1 L4143-4266): the per-copy sync-pair core packaged from the carrier-elder pigeonhole (hr_carrier_elder_pair) plus the green lift/birth/sync machinery (alive_cell_lift, image_birth_upper_bound, image_birth_strong_lower_bound, diagram_sync_high_separation, sync_comerge_images) — the packaged input for the merge-level extraction and the value cases of the hr-route fiber census.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem hr_sync_pair_lift {ιX ιY : Type*}
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
    {b d δx η₀ : ℝ} (hbd : d < b) (hαd : α < d)
    (hgap : (∀ τ ∈ critSet hTameX, τ ≠ b → δx < |τ - b|) ∧
      (∀ τ ∈ critSet hTameX, τ ≠ d → δx < |τ - d|))
    (hη₀0 : 0 < η₀) (hη₀δ : η₀ < δx) (hη₀bd : η₀ < (b - d) / 2)
    (hη₀sep : η₀ < b - d - 2 * ε) (hη₀α : η₀ < d - α)
    (hmult : mult (rankFn stageX JX) ((b : EReal), (d : EReal)) ≠ 0) :
    ∃ (C₁ C₂ : comps stageX JX (d + η₀)) (A₁ A₂ : comps stageX JX (d + η₀ + 2 * ε)),
      birthSup hLawX (d + η₀) C₁ = b ∧
      b ≤ birthSup hLawX (d + η₀) C₂ ∧ C₁ ≠ C₂ ∧
      structMap hLawX (show d - η₀ ≤ d + η₀ by linarith) C₁
        = structMap hLawX (show d - η₀ ≤ d + η₀ by linarith) C₂ ∧
      birthSup hLawX (d + η₀ + 2 * ε) A₁ = b ∧
      birthSup hLawX (d + η₀ + 2 * ε) A₂ = birthSup hLawX (d + η₀) C₂ ∧
      structMap hLawX (show d + η₀ ≤ d + η₀ + 2 * ε by linarith) A₁ = C₁ ∧
      structMap hLawX (show d + η₀ ≤ d + η₀ + 2 * ε by linarith) A₂ = C₂ ∧
      b - ε ≤ birthSup hLawY ((d + η₀ + 2 * ε) - ε)
          (φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₁) ∧
      birthSup hLawY ((d + η₀ + 2 * ε) - ε)
          (φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₁) ≤ b + ε ∧
      φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₁
        ≠ φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₂ ∧
      structMap hLawY (show (d - η₀) - ε ≤ (d + η₀ + 2 * ε) - ε by linarith)
          (φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₁)
        = structMap hLawY (show (d - η₀) - ε ≤ (d + η₀ + 2 * ε) - ε by linarith)
          (φ (d + η₀ + 2 * ε) (show α ≤ d + η₀ + 2 * ε by linarith) A₂)
    := by sorry
