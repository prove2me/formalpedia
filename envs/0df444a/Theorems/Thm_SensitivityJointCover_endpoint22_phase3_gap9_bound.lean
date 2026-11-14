-- Prove2me | Theorems.Thm_SensitivityJointCover_endpoint22_phase3_gap9_bound
-- name    : SensitivityJointCover.endpoint22_phase3_gap9_bound
-- status  : Proved
-- author  : @jennyuxi
-- created : 2026-11-13T08:10:18.543243+00:00
-- url     : https://prove2.me/theorems/ae4c10fa-8aa7-4286-b0a0-043bdfe6e6bd
-- title:
--   Joint cover for the state-9 gap in the actual final phase
-- statement:
--   Let $F_0,\ldots,F_{21}$ be nested Boolean predicates on a finite child-coordinate type: $F_j(y)=1$ implies $F_i(y)=1$ for $i\le j$. Apply phase index 3, the actual fourth phase of the published 22-state construction, to obtain parent predicates $G_0,\ldots,G_{21}$. The graph is a loopless tournament on 5591 vertices with binary edge labels.
--
--   Assume the existing source exclusion: if a vertex $v$ points to every vertex of a disjoint set $A$, and a binary coloring of $A$ makes every edge from $A\cup\{v\}$ into $A$ agree with its head's color, then $|A|\le18$. This is the unchanged candidate-cap interface $\mathrm{DominatorCardBound}(1,19)$.
--
--   Assume two uniform child bounds. At every input with $F_{17}=1$, at most $2041395696528705380$ coordinate flips make $F_{14}$ false. At every input with $F_{11}=0$, at most $98368454968486$ coordinate flips make $F_{18}$ true.
--
--   Then every parent input $x$ with $G_9(x)=1$ and $G_{10}(x)=0$ satisfies
--
--   $$
--   \left|\{z:G_4(x^{\{z\}})=0\}\cup\{z:G_{13}(x^{\{z\}})=1\}\right|
--   \le4084562025246843508.
--   $$
--
--   Here $x^{\{z\}}$ flips coordinate $z$. This is a global conditional bound over all parent inputs and all repair signatures, for the actual state-13 target 18 and guard 6. No cap-attainability or nonempty child-coordinate assumption is made. It supplies a supporting profile-transfer inequality; it does not assert an improved full-cycle multiplier or separation exponent.
-- source:
--   Original joint-cover deduction for phase index 3, entries 4, 9, 10, and 13, of Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe (Endpoint22Recipes): https://prove2.me/definitions/c0e9ff4f-3de6-4821-bfbd-0a95cc15178b. Uses the unchanged ResidualCaps.DominatorCardBound source interface with cutoff 19 (pcross=18). Child-profile constants are profileTable3 B(14,17) and A(11,18) of the existing 2.13981 construction https://prove2.me/theorems/0e93b146-3cac-42d3-b8f4-74010d06b636, by @yousofy with Codex, retaining its OpenAI/math and earlier community attribution. Related accepted final-phase joint cover: https://prove2.me/theorems/0488338f-e65e-41f2-ac40-2e9f7cb29b5a. The present proof uses the different shared gap G9=true,G10=false and excludes all guard repairs at the selected witness. No new cycle or exponent is asserted.

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

theorem SensitivityJointCover.endpoint22_phase3_gap9_bound {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : Sensitivity213981Formal.ResidualCaps.DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 14 17 2041395696528705380)
 (hS : ABound F 11 18 98368454968486)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 9 x=true → parent S F 10 x=false →
 (flipsTo (parent S F 4) false x ∪ flipsTo (parent S F 13) true x).card≤4084562025246843508 := by sorry
