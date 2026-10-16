-- Prove2me | Theorems.Thm_PersistClust_Count_t5_deathKill
-- name    : PersistClust.Count.t5_deathKill
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T12:41:26.545467+00:00
-- url     : https://prove2.me/theorems/a4e409b6-3eb8-48fb-aed4-1ab0ccfb8d97
-- title:
--   Death-kill (phi-side): the census-injection configuration with an outliver is impossible
-- statement:
--   The interleaving setup: X and Y are one-parameter persistence modules of finite components (comps families with structure maps under filtration laws, both tame), phi maps X-levels down eps to Y-levels and psi maps Y-levels down eps to X-levels, and the four square laws (descent compatibility of each map, and the two round-trip identities) hold. The count-gap configuration of the companion lemma is IMPOSSIBLE. Fix levels with beta at least alpha and a window bound s at least beta + eps. Assume: every Y-cell at the pullback level beta - eps was born strictly above s; no X-cell at level beta was born exactly at s - eps; there is an outliver Y-cell O at the pullback level avoided by the phi-image of every X-cell at level beta born above s - eps; and phi identifies X-cells at level beta born above s - eps. Then False: the count-gap lemma makes the X-window rank strictly below the Y-window rank, while the psi-side window inequality over the same window bounds the Y-rank by the X-rank -- together a contradiction. The lemma eliminates this census configuration outright.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the death-kill (phi-side) of the interleaving rank calculus. Transcribed GREEN (exit 0, sorry-free) from the working file; the helper chain is inlined verbatim above the target (rank-original readings, rank-equals-structure-image forms, the window inequality for the kill pair, the companion count lemma for the kill pair); the module structures rely on the platform Definitions via imports.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem t5_deathKill {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
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
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {s β : ℝ} (hβα : α ≤ β) (hwin : β - ε + 2 * ε ≤ s)
    (hcountY : ∀ C : comps stageY JY (β - ε), s < birthSup hLawY (β - ε) C)
    (hgenX : ∀ D : comps stageX JX β, s - ε ≠ birthSup hLawX β D)
    (hO : ∃ O : comps stageY JY (β - ε), ∀ D : comps stageX JX β,
        s - ε < birthSup hLawX β D → φ β hβα D ≠ O)
    (hinj : ∀ D₁ D₂ : comps stageX JX β, s - ε < birthSup hLawX β D₁ →
        s - ε < birthSup hLawX β D₂ → φ β hβα D₁ = φ β hβα D₂ → D₁ = D₂) : False
    := by sorry
