-- Prove2me | Theorems.Thm_SensitivityJointCover_endpoint22_phase3_gap15_bound
-- name    : SensitivityJointCover.endpoint22_phase3_gap15_bound
-- status  : Proved
-- author  : @jennyuxi
-- created : 2026-11-14T02:17:52.341296+00:00
-- url     : https://prove2.me/theorems/41c3626e-41ff-47b5-8da1-6ab7930f06eb
-- title:
--   State-15-gap joint cover with zero-tolerance external guards and self-target repairs
-- statement:
--   Let $F_0,\ldots,F_{21}$ be nested Boolean predicates on a finite coordinate set: $F_j(y)=1$ implies $F_i(y)=1$ for $i\le j$. Let $G_0,\ldots,G_{21}$ be the parent predicates produced by the fourth phase (index 3) of the published 22-state construction. The underlying graph is a loopless tournament on 5591 vertices, each having 2795 outgoing neighbors, with binary labels on ordered vertex pairs.
--
--   Assume the following uniform bounds on child-coordinate flips:
--
--   * Where $F_{20}(y)=1$, at most $53874150507309062240$ flips make $F_{15}$ false.
--   * Where $F_0(y)=0$, at most $1330073126471840$ flips make $F_{13}$ true.
--   * Where $F_{20}(y)=1$ and $F_{21}(y)=0$, the union of flips making $F_{15}$ false and flips making $F_{21}$ true has size at most $56530689653409078976$.
--
--   Then every parent input $x$ satisfying $G_{15}(x)=1$ and $G_{16}(x)=0$ obeys
--   $$
--   \left|\{z:G_7(x^{\{z\}})=0\}\cup\{z:G_{16}(x^{\{z\}})=1\}\right|\le114122394549206934016.
--   $$
--   Here $x^{\{z\}}$ denotes a single coordinate flip. This bound includes every repair signature, both outside the selected state-15 witness and at the witness itself, and retains the external guard changes relevant to state 7's zero tolerance. No candidate-cap hypothesis is required. This supporting conditional inequality does not assert a new cycle integer multiplier or separation exponent.
-- source:
--   Original deduction for the unchanged fourth-phase Endpoint22Recipes, https://prove2.me/definitions/c0e9ff4f-3de6-4821-bfbd-0a95cc15178b. Child constants are profileTable3 B(15,20), A(0,13), and D(15,20,21) of the existing 2.13981 construction https://prove2.me/theorems/0e93b146-3cac-42d3-b8f4-74010d06b636 by @yousofy with Codex, retaining its OpenAI/math and earlier community attribution. Adapts the accepted state-8-gap cover https://prove2.me/theorems/9f9cf4a6-1976-4b1f-a6f1-a3e328488d4f while retaining the larger self-repair child joint bound. The general bound is max(2B,B+J)+2795A. No candidate cap or exponent improvement is assumed.

import Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Prod
import Lean
open Sensitivity213981Formal Sensitivity213981Formal.ThreeBoundWitness
open Sensitivity213981Formal.ThreeBoundProfiles
open scoped Classical
set_option autoImplicit false

theorem SensitivityJointCover.endpoint22_phase3_gap15_bound {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hd : ∀ v, (Finset.univ.filter (Adj v)).card=2795)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 15 20 53874150507309062240)
 (hA : ABound F 0 13 1330073126471840)
 (hJ : ∀ y, F 20 y=true → F 21 y=false →
   (flipsTo (F 15) false y ∪ flipsTo (F 21) true y).card≤56530689653409078976)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 15 x=true → parent S F 16 x=false →
 (flipsTo (parent S F 7) false x ∪ flipsTo (parent S F 16) true x).card≤114122394549206934016 := by sorry
