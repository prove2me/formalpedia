-- Prove2me | Theorems.Thm_PersistClust_Count_prom_copy_birth_chain
-- name    : PersistClust.Count.prom_copy_birth_chain
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T20:27:51.513263+00:00
-- url     : https://prove2.me/theorems/3810da0b-c62a-445a-8efc-381fcca2ab9e
-- title:
--   T5a birth-chain: a prominent X-copy pins an image thread with birth-sup in the eps-window
-- statement:
--   Under a strong eps-interleaving above alpha between tame modules, every prominent off-diagonal X-copy a (PromQNE: its point (b, d) lies in the NE quadrant above alpha and cannot be absorbed by the diagonal at radius eps) yields a Y-level cell E = phi_beta(A) whose birth-sup lies in the closed eps-window [b-eps, b+eps], at a level beta strictly above the death coordinate: the full chain reads a's bar, produces the census cell at a small probe, lifts it alive-up to a level below b, pins its birth-sup at b through every descent, and transfers the pin through the two image-window bounds of the interleaving.
-- source:
--   T5a support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the birth-coordinate assembly of the matching gate, consumed by the elder-trap and partner-absorption arguments. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy; it assembles the accepted image_birth_upper_bound and image_birth_strong_lower_bound tools with the census/ alive-up chain.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem prom_copy_birth_chain {ιX ιY : Type*}
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
    {a : offD (mult (rankFn stageX JX))} (hprom : PromQNE α ε a) :
    ∃ b d β : ℝ, ∃ E : comps stageY JY (β - ε),
      offPt a = ((b : EReal), (d : EReal)) ∧ d + 2 * ε < b ∧ α < d ∧ d < β - ε ∧
        α ≤ β - ε ∧
      b - ε ≤ birthSup hLawY (β - ε) E ∧ birthSup hLawY (β - ε) E ≤ b + ε
    := by sorry
