-- Prove2me | Theorems.Thm_SensitivityJointCover_endpoint22_phase3_gap11_bound
-- name    : SensitivityJointCover.endpoint22_phase3_gap11_bound
-- status  : Proved
-- author  : @jennyuxi
-- created : 2026-11-14T00:35:42.916727+00:00
-- url     : https://prove2.me/theorems/2da5d971-3db4-4895-9c2a-cf54bce1d8b4
-- title:
--   Final-phase state-11-gap joint cover retaining the external child interval
-- statement:
--   Let $F_0,\ldots,F_{21}$ be nested Boolean predicates on a finite child-coordinate type: $F_j(y)=1$ implies $F_i(y)=1$ for $i\le j$. Apply phase index 3, the actual fourth phase of the published 22-state construction, to obtain parent predicates $G_0,\ldots,G_{21}$. The graph is a loopless tournament on 5591 vertices with binary edge labels.
--
--   Assume the existing source exclusion: if a vertex $v$ points to every vertex of a disjoint set $A$, and a binary coloring of $A$ makes every edge from $A\cup\{v\}$ into $A$ agree with its head's color, then $|A|\le18$. This is the unchanged candidate-cap interface $\mathrm{DominatorCardBound}(1,19)$.
--
--   Assume these uniform child-coordinate bounds:
--
--   * Where $F_{17}=1$, at most $2041395696528705380$ flips make $F_{14}$ false.
--   * Where $F_7=1,F_8=0$, at most $150358948041692066811$ flips make $F_6$ false.
--   * Where $F_8=1,F_9=0$, at most $146185162351149245833$ flips make $F_6$ false.
--   * Where $F_9=0$, at most $98368454968486$ flips make $F_{18}$ true.
--   * Where $F_{17}=1,F_{18}=0$, at most $2871710707230501566$ flips make $F_{18}$ true.
--
--   Then every parent input $x$ with $G_{11}(x)=1$ and $G_{12}(x)=0$ satisfies
--
--   $$
--   \left|\{z:G_3(x^{\{z\}})=0\}\cup\{z:G_{13}(x^{\{z\}})=1\}\right|
--   \le154443510066938910319.
--   $$
--
--   Here $x^{\{z\}}$ flips coordinate $z$. This is a global conditional transfer bound for every repair signature of the actual recipe, including self-target repairs at the selected state-11 witness. All graph, cap, nestedness, and child-bound hypotheses are explicit. No cap attainability, positive abstract counting bound, or nonempty child-coordinate assumption is made. This supporting inequality does not assert an improved full-cycle integer multiplier or separation exponent.
-- source:
--   Original joint-cover deduction for phase index 3, entries 3, 11, 12, and 13 of Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe (Endpoint22Recipes): https://prove2.me/definitions/c0e9ff4f-3de6-4821-bfbd-0a95cc15178b. Uses the unchanged ResidualCaps.DominatorCardBound source interface with cutoff 19. Child constants are profileTable3 B(14,17), M(6,7), M(6,8), A(9,18), and P(17,18) of the existing 2.13981 construction https://prove2.me/theorems/0e93b146-3cac-42d3-b8f4-74010d06b636, by @yousofy with Codex, retaining its OpenAI/math and earlier community attribution. Related verified self-repair cover: https://prove2.me/theorems/39ba2170-a38c-4ad8-a0c1-431395ec94e4. This proof retains the external interval F7=true,F9=false and the zero guard-9 condition at the selected witness. No new cycle integer multiplier or exponent is asserted.

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

theorem SensitivityJointCover.endpoint22_phase3_gap11_bound {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : Sensitivity213981Formal.ResidualCaps.DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 14 17 2041395696528705380)
 (hM7 : ∀ y, F 7 y=true → F 8 y=false → (flipsTo (F 6) false y).card≤150358948041692066811)
 (hM8 : ∀ y, F 8 y=true → F 9 y=false → (flipsTo (F 6) false y).card≤146185162351149245833)
 (hS : ABound F 9 18 98368454968486)
 (hQ : ∀ y, F 17 y=true → F 18 y=false → (flipsTo (F 18) true y).card≤2871710707230501566)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 11 x=true → parent S F 12 x=false →
 (flipsTo (parent S F 3) false x ∪ flipsTo (parent S F 13) true x).card≤154443510066938910319 := by sorry
