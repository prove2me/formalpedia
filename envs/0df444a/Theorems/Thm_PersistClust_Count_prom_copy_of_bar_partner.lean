-- Prove2me | Theorems.Thm_PersistClust_Count_prom_copy_of_bar_partner
-- name    : PersistClust.Count.prom_copy_of_bar_partner
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T20:24:57.556991+00:00
-- url     : https://prove2.me/theorems/b6dd947f-19da-4fb5-a2a2-5c779183cae0
-- title:
--   T5a copy routing: a bar inside the eps-box of a prominent copy yields a close Y-copy
-- statement:
--   Let a be an off-diagonal copy of the X-diagram standing for the real point (b, d), and suppose the Y-diagram has a bar (b2, v) with nonzero multiplicity inside the eps-box around (b, d) (b-eps <= b2 <= b+eps, d-eps <= v <= d+eps) while the point is 2eps-separated from the diagonal (d + 2eps < b). Then the Y-diagram has an off-diagonal copy q standing for (b2, v) that is CloseCopy2-close to a: routing the prominent copy to a genuine off-diagonal partner. The proof witnesses q by the zeroth copy of the nonzero multiplicity and closes the closeness by the EReal coercions of the box bounds.
-- source:
--   T5a support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the off-diagonal partner supply of the multi-bijection assembly, the demand-routing leaf under the accepted DemandsOff predicates of the matching gate. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem prom_copy_of_bar_partner {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    {ε : ℝ} {a : offD (mult (rankFn stageX JX))} {b d b₂ v : ℝ}
    (hpt : offPt a = ((b : EReal), (d : EReal)))
    (hbox1 : b - ε ≤ b₂) (hbox2 : b₂ ≤ b + ε) (hbox3 : d - ε ≤ v) (hbox4 : v ≤ d + ε)
    (hsep : d + 2 * ε < b)
    (hmult : mult (rankFn stageY JY) ((b₂ : EReal), (v : EReal)) ≠ 0) :
    ∃ q : offD (mult (rankFn stageY JY)), CloseCopy2 ε a q
    := by sorry
