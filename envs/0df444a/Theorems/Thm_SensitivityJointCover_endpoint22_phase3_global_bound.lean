-- Prove2me | Theorems.Thm_SensitivityJointCover_endpoint22_phase3_global_bound
-- name    : SensitivityJointCover.endpoint22_phase3_global_bound
-- status  : Proved
-- author  : @jennyuxi
-- created : 2026-11-13T06:28:16.944083+00:00
-- url     : https://prove2.me/theorems/0488338f-e65e-41f2-ac40-2e9f7cb29b5a
-- title:
--   Global joint cover for states 4, 10, 11, and 21 of the actual final phase
-- statement:
--   Let $F_0,\ldots,F_{21}$ be nested Boolean predicates on a finite child-coordinate type: $F_j(y)=1$ implies $F_i(y)=1$ whenever $i\le j$. Apply phase index 3, the actual fourth phase of the published 22-state construction, to obtain parent predicates $G_0,\ldots,G_{21}$. The underlying directed graph is a loopless tournament on 5591 vertices, with binary edge labels.
--
--   Assume the source exclusion from the existing candidate-cap certificates. Explicitly, if a vertex $v$ points to every vertex of a disjoint set $A$, and there is a binary coloring of $A$ such that every edge from $A\cup\{v\}$ into $A$ agrees with the color of its head, then $|A|\le18$. In the formal statement this is the unchanged interface $\mathrm{DominatorCardBound}(1,19)$.
--
--   Assume three uniform child-profile bounds. At any child input where $F_{17}=1$, at most $2041395696528705380$ coordinate flips make $F_{14}$ false. Where $F_9=1$, at most $3056915546137949758$ coordinate flips make $F_0$ false. Where $F_{11}=0$, at most $98368454968486$ coordinate flips make $F_{21}$ true.
--
--   Then every parent input $x$ satisfying $G_{10}(x)=1$ and $G_{11}(x)=0$ obeys
--
--   $$
--   \left|\{z:G_4(x^{\{z\}})=0\}\cup\{z:G_{21}(x^{\{z\}})=1\}\right|
--   \le7141477571384793266.
--   $$
--
--   Here $x^{\{z\}}$ flips the single coordinate $z$. The count concerns coordinates, including overlaps, rather than separately counting witness rows.
--
--   This is a conditional global transfer theorem for the unchanged actual final-phase recipe. It covers every repair signature and uses the existing source cap as an upper bound, without requiring any cap to be attained. Its graph, cap, nestedness, and child-profile hypotheses are explicit. It does not establish a complete improved four-phase cycle certificate or a separation exponent, and it assumes no nonempty child-coordinate type.
-- source:
--   Original joint-cover deduction for phase index 3, entries 4, 10, 11, and 21, of Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe (Endpoint22Recipes): https://prove2.me/definitions/c0e9ff4f-3de6-4821-bfbd-0a95cc15178b. Uses the unchanged ResidualCaps.DominatorCardBound interface and the source clause of the existing candidate-cap certificate (pcross=18, hence exclusion cutoff 19). Child-profile constants from profileTable3 of the existing 2.13981 construction https://prove2.me/theorems/0e93b146-3cac-42d3-b8f4-74010d06b636, by @yousofy with Codex, retaining its OpenAI/math and earlier community attribution. Generalizes the previously locally verified maximal two-head overlap argument to all repair signatures. This contribution proves the stated conditional transfer, not a new full-cycle certificate or exponent.

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

theorem SensitivityJointCover.endpoint22_phase3_global_bound {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hcap : Sensitivity213981Formal.ResidualCaps.DominatorCardBound Adj label 1 19)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 14 17 2041395696528705380)
 (hG : BBound F 0 9 3056915546137949758)
 (hS : ABound F 11 21 98368454968486)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 10 x=true → parent S F 11 x=false →
 (flipsTo (parent S F 4) false x ∪ flipsTo (parent S F 21) true x).card≤7141477571384793266 := by sorry
