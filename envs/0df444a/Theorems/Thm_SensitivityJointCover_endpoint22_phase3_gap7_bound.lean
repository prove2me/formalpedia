-- Prove2me | Theorems.Thm_SensitivityJointCover_endpoint22_phase3_gap7_bound
-- name    : SensitivityJointCover.endpoint22_phase3_gap7_bound
-- status  : Proved
-- author  : @jennyuxi
-- created : 2026-11-13T21:55:46.532705+00:00
-- url     : https://prove2.me/theorems/39ba2170-a38c-4ad8-a0c1-431395ec94e4
-- title:
--   Joint cover including self-repair for the final-phase state-7 gap
-- statement:
--   Let $F_0,\ldots,F_{21}$ be nested Boolean predicates on a finite child-coordinate type: $F_j(y)=1$ implies $F_i(y)=1$ for $i\le j$. Apply phase index 3, the actual fourth phase of the published 22-state construction, to obtain parent predicates $G_0,\ldots,G_{21}$. The graph is a loopless tournament on 5591 vertices with binary edge labels.
--
--   Assume the existing source exclusion: if a vertex $v$ points to every vertex of a disjoint set $A$, and a binary coloring of $A$ makes every edge from $A\cup\{v\}$ into $A$ agree with its head's color, then $|A|\le18$. This is the unchanged candidate-cap interface $\mathrm{DominatorCardBound}(1,19)$.
--
--   Assume the following uniform child-coordinate bounds:
--
--   * Where $F_{15}=1$, at most $2041395696528705380$ flips make $F_{14}$ false.
--   * Where $F_{11}=1$, at most $3056915546137949758$ flips make $F_6$ false.
--   * Where $F_{13}=0$, at most $3750242918035586$ flips make $F_{18}$ true.
--   * Where $F_{15}=1$ and $F_{16}=0$, at most $108524743996953688$ flips make $F_{18}$ true.
--
--   Then every parent input $x$ with $G_7(x)=1$ and $G_8(x)=0$ satisfies
--
--   $$
--   \left|\{z:G_4(x^{\{z\}})=0\}\cup\{z:G_{13}(x^{\{z\}})=1\}\right|
--   \le7207211311720001066.
--   $$
--
--   Here $x^{\{z\}}$ flips coordinate $z$. This is a global conditional transfer bound for all repair signatures of the actual recipe. It includes the possibility that the selected state-7 witness is itself a state-13 target-repair candidate. No cap or child-count attainability, positivity of abstract counting bounds, or nonempty child-coordinate assumption is made. It does not assert an improved full-cycle integer multiplier or separation exponent.
-- source:
--   Original joint-cover deduction for phase index 3, entries 4, 7, 8, and 13 of Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe (Endpoint22Recipes): https://prove2.me/definitions/c0e9ff4f-3de6-4821-bfbd-0a95cc15178b. Uses the unchanged ResidualCaps.DominatorCardBound source interface with cutoff 19 (pcross=18). Child bounds are profileTable3 B(14,15), B(6,11), A(13,18), and P(15,18) of the existing 2.13981 construction https://prove2.me/theorems/0e93b146-3cac-42d3-b8f4-74010d06b636, by @yousofy with Codex, retaining its OpenAI/math and earlier community attribution. Related accepted state-9-gap cover: https://prove2.me/theorems/ae4c10fa-8aa7-4286-b0a0-043bdfe6e6bd. The present proof treats the different state-7 gap and explicitly removes the witness from the target-candidate set before invoking the source exclusion. No new exponent or improved full-cycle integer multiplier is asserted.

import Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Prod
import Lean
open Sensitivity213981Formal Sensitivity213981Formal.ThreeBoundWitness
open Sensitivity213981Formal.ThreeBoundProfiles
open scoped Classical
set_option autoImplicit false

theorem SensitivityJointCover.endpoint22_phase3_gap7_bound {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : Sensitivity213981Formal.ResidualCaps.DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 14 15 2041395696528705380)
 (hG : BBound F 6 11 3056915546137949758)
 (hS : ABound F 13 18 3750242918035586)
 (hQ : ∀ y, F 15 y=true → F 16 y=false →
   (flipsTo (F 18) true y).card≤108524743996953688)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 7 x=true → parent S F 8 x=false →
 (flipsTo (parent S F 4) false x ∪ flipsTo (parent S F 13) true x).card≤7207211311720001066 := by sorry
