-- Prove2me | Theorems.Thm_StrongPerfectGraph_OddPrism_banister_rung_odd
-- name    : StrongPerfectGraph.OddPrism.banister_rung_odd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:30:26.266442+00:00
-- url     : https://prove2.me/theorems/e5db3c8a-ed2f-48fd-a4fc-e937e818a44f
-- title:
--   11.3, p. 129 — in a Berge graph with no even prism, rungs and banisters have odd length
-- statement:
--   Let $G$ be a Berge graph containing no even prism, let $S=(A,C,B)$ be a step-connected strip in $G$, and let $a_0\text{-}R_0\text{-}b_0$ be a banister with respect to $S$. Then
--   $$\text{every rung of } S \text{ has odd length, and so does } R_0 .$$
--
--   Odd parity of the rungs and of the banister is used throughout Sections 12 and 13, in particular to see that the banister of a staircase has odd length at least $3$.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 129, 11.3

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStepConnectedStrip
import Definitions.Def_StrongPerfectGraph_OddPrism_IsStaircase

namespace StrongPerfectGraph.OddPrism

/-- **11.3** (p. 129). Let `G` be Berge, containing no even prism, let `S = (A, C, B)` be a
step-connected strip in `G`, and let `a₀-R₀-b₀` be a banister. Then every rung of the strip
has odd length, and so does `R₀`. -/
theorem banister_rung_odd {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsBerge G) (hprism : ¬ ContainsEvenPrism G)
    (A C B : Set V) (hS : IsStepConnected G A C B)
    (r₀ : List V) (hr₀ : IsBanister G A C B r₀) :
    (∀ r : List V, IsRung G A C B r → Odd (r.length - 1)) ∧ Odd (r₀.length - 1) := by sorry

end StrongPerfectGraph.OddPrism
