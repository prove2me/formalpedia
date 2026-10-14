-- Prove2me | Theorems.Thm_PersistClust_Count_image_merge_lands_in_box
-- name    : PersistClust.Count.image_merge_lands_in_box
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T17:23:27.105703+00:00
-- url     : https://prove2.me/theorems/41cd4296-c2c2-4a4a-994c-d6c867e8a9e3
-- title:
--   Image-pair coalescence level lands in the eps-box (interleaved merge pin)
-- statement:
--   Two filtered cluster modules X and Y are strongly eps-interleaved above a level alpha: phi maps X-component classes at every level gamma >= alpha to Y-component classes at level gamma - eps and commutes with descent (square (i')), while psi maps Y-component classes at level gamma back to X-component classes at level gamma - eps with psi_{gamma-eps}(phi_gamma(x)) equal to the (gamma-2eps)-descent of x (square (iv')). Let beta >= d >= alpha. Suppose the X-classes A1, A2 at level beta descend to DISTINCT classes M1 != M2 at level d. If the phi-images of A1 and A2 at level beta coincide after descending to level d - eps (the seed), then the pair's 2-to-1 image coalescence level is pinned inside the box [d - eps, d + eps]: there exists a real m' with d - eps <= m' <= d + eps such that the descended image pair coincides at every level u - eps with d <= u and u - eps < m', differs at every level u - eps with d <= u and m' < u - eps, and coincides at the seed level d - eps.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the SLIVER-II equal-arm in-branch construction of the rank-level kill (t5_l1_rankKill R2 stage 1, rankR1) — a seeded d-eps image coincidence localizes the interleaved pair's image merge level inside the [d-eps, d+eps] box via down-persistence (no critical-freeness) and the interleaving squares; the in-box death pin consumed by the merge-census dispatch.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem image_merge_lands_in_box {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {d β : ℝ} (hαd : α ≤ d) (hαβ : α ≤ β) (hdβ : d ≤ β)
    (A₁ A₂ : comps stageX JX β) (M₁ M₂ : comps stageX JX d)
    (hA₁d : structMap hLawX hdβ A₁ = M₁)
    (hA₂d : structMap hLawX hdβ A₂ = M₂)
    (hMne : M₁ ≠ M₂)
    (hseed : structMap hLawY (show d - ε ≤ β - ε by linarith) (φ β hαβ A₁) =
      structMap hLawY (show d - ε ≤ β - ε by linarith) (φ β hαβ A₂)) :
    ∃ (m' : ℝ), d - ε ≤ m' ∧ m' ≤ d + ε ∧
        (∀ (u : ℝ) (huε : u - ε ≤ β - ε) (hud : d ≤ u), u - ε < m' →
           structMap hLawY huε (φ β hαβ A₁) =
           structMap hLawY huε (φ β hαβ A₂)) ∧
        (∀ (u : ℝ) (huε : u - ε ≤ β - ε) (hud : d ≤ u), m' < u - ε →
           structMap hLawY huε (φ β hαβ A₁) ≠
           structMap hLawY huε (φ β hαβ A₂)) ∧
        structMap hLawY (show d - ε ≤ β - ε by linarith) (φ β hαβ A₁) =
          structMap hLawY (show d - ε ≤ β - ε by linarith)
            (φ β hαβ A₂)
    := by sorry
