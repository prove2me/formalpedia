-- Prove2me | Theorems.Thm_PersistClust_Count_t5_pullbackBirthUpper
-- name    : PersistClust.Count.t5_pullbackBirthUpper
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T11:49:54.725705+00:00
-- url     : https://prove2.me/theorems/02d0a8ee-f6e4-4eca-8ca5-5d52d0406c56
-- title:
--   Pullback birth-upper bound: the psi-pullback of a Y-cell has birth-sup at most b + eps when its 2eps-descent has birth-sup b
-- statement:
--   Let X and Y be one-parameter persistence modules of finite components: families comps_X(level), comps_Y(level) of component sets over the reals, connected by structure maps under filtration laws, with Y tame. Fix eps >= 0 and a threshold alpha, and assume interleaving maps phi (from X-levels to Y-levels shifted down by eps) and psi (from Y-levels to X-levels shifted down by eps) satisfying the two square laws: (i') phi commutes with descent along level inclusions, and (iii') the phi-psi round trip from a Y-component back to Y agrees with the ordinary 2eps-descent of the source component. Then: for any Y-component C at a level beta above alpha, if the birth supremum of C's 2eps-descent (at level beta - eps - eps) equals b, the birth supremum of the psi-pullback psi_beta(C) at level beta - eps is at most b + eps. This is the psi-side (backward) companion of the image birth-sup bounds: pullbacks cannot be born much later than the descent chain they came from. It is a rung of the interleaving birth-sup calculus used in the persistence-clustering matching arguments: components, structure maps, birth suprema and tameness are the platform's comps/structMap/birthSup/IsTameModule structures.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the psi-side pullback birth-upper bound under the interleaving squares (i') and (iii'), the backward rung of the birth-sup transfer calculus. Transcribed GREEN (exit 0, sorry-free) from the working file; the 4-declaration helper chain (structMap composition, the structMap identity, the level bound on birth-suprema, and the descent monotonicity of birth-suprema) inlined verbatim above the target.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem t5_pullbackBirthUpper {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameY : IsTameModule stageY JY) {α ε : ℝ} (hε : 0 ≤ ε)
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq3 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (y : comps stageY JY β),
      φ (β - ε) hβε (ψ β hβ y) =
        structMap hLawY (show (β - ε) - ε ≤ β by linarith) y)
    {β b : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε)
    (C : comps stageY JY β)
    (hDesc : birthSup hLawY ((β - ε) - ε)
        (structMap hLawY (show (β - ε) - ε ≤ β by linarith) C) = b) :
    birthSup hLawX (β - ε) (ψ β hβ C) ≤ b + ε
    := by sorry
