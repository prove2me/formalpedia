-- Prove2me | Theorems.Thm_PersistClust_Count_phi_fiber_merge
-- name    : PersistClust.Count.phi_fiber_merge
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T13:31:26.068073+00:00
-- url     : https://prove2.me/theorems/caccc431-22a4-4649-8268-d19577290f68
-- title:
--   Phi-fiber merge (square iv): phi-identified X-cells have equal 2eps-descent structure maps
-- statement:
--   The interleaving setup: X and Y are one-parameter persistence modules of finite components (comps families with structure maps under filtration laws), phi maps X-levels down eps to Y-levels and psi maps Y-levels down eps to X-levels. Assume the square law (iv): psi at the pullback level of the phi-image of any X-cell x equals the 2eps-descent structure map of x. If phi identifies two X-cells x and x' at a common level beta at least alpha (with the pullback level also at least alpha), then the 2eps-descent structure maps of x and x' agree: the phi-fiber carries the equality down to the source descent.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the phi-fiber merge (square iv) of the interleaving rank calculus. Transcribed GREEN (exit 0, sorry-free) from the working file; the platform mirror structures (comps/structMap/compRep/offD) rely on the platform Definitions via imports.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem phi_fiber_merge {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {β : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε) {x x' : comps stageX JX β}
    (hφ : φ β hβ x = φ β hβ x') :
    structMap hLawX (show (β - ε) - ε ≤ β by linarith) x =
      structMap hLawX (show (β - ε) - ε ≤ β by linarith) x'
    := by sorry
