-- Prove2me | Theorems.Thm_SensitivityJointCover_endpoint22_phase3_gap8_bound
-- name    : SensitivityJointCover.endpoint22_phase3_gap8_bound
-- status  : Proved
-- author  : @jennyuxi
-- created : 2026-11-14T01:12:30.514234+00:00
-- url     : https://prove2.me/theorems/9f9cf4a6-1976-4b1f-a6f1-a3e328488d4f
-- title:
--   State-8-gap joint cover retaining zero-tolerance guard destruction
-- statement:
--   Let $F_0,\ldots,F_{21}$ be nested Boolean predicates on a finite coordinate set: $F_j(y)=1$ implies $F_i(y)=1$ for $i\le j$. Let $G_0,\ldots,G_{21}$ be the parent predicates obtained by applying the fourth phase (index 3) of the published 22-state construction to these predicates. The underlying graph is a loopless tournament on 5591 vertices, each with exactly 2795 outgoing neighbors, and each ordered vertex pair has a binary label.
--
--   Assume the following uniform bounds on child-coordinate flips:
--
--   * If $F_{16}(y)=1$, at most $53874150507309062240$ flips make $F_{15}$ false.
--   * If $F_{11}(y)=0$, at most $1330073126471840$ flips make $F_{13}$ true.
--   * If $F_{16}(y)=1$ and $F_{17}(y)=0$, the union of the flips making $F_{15}$ false and those making $F_{18}$ true has size at most $53874150507309062240$.
--
--   Then every parent input $x$ satisfying $G_8(x)=1$ and $G_9(x)=0$ obeys
--   $$\left|\{z:G_7(x^{\{z\}})=0\}\cup\{z:G_{12}(x^{\{z\}})=1\}\right|\le111465855403106917280.$$
--   Here $x^{\{z\}}$ denotes a single coordinate flip. The bound covers every repair signature, including repairs at the selected witness itself, and retains the outside guard changes relevant to state 7's zero tolerance. It requires no candidate-cap hypothesis. This is a supporting conditional inequality; it makes no claim of a new separation exponent.
-- source:
--   Original deduction for the unchanged Endpoint22Recipes fourth phase, https://prove2.me/definitions/c0e9ff4f-3de6-4821-bfbd-0a95cc15178b. Uses child profileTable3 B(15,16), A(11,13), D(15,16,18) from the existing 2.13981 construction https://prove2.me/theorems/0e93b146-3cac-42d3-b8f4-74010d06b636, by @yousofy with Codex, retaining its OpenAI/math and earlier community attribution. The joint bound is max(2B,B+J)+2795A. No candidate-cap assumption or improved exponent is asserted.

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

theorem SensitivityJointCover.endpoint22_phase3_gap8_bound {I : Type} [Fintype I]
 (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬Adj v v)
 (label : Fin 5591 → Fin 5591 → Bool)
 (htor : ∀ v r, v≠r → (Adj v r ↔ ¬Adj r v))
 (hd : ∀ v, (Finset.univ.filter (Adj v)).card=2795)
 (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
 (hB : BBound F 15 16 53874150507309062240)
 (hA : ABound F 11 13 1330073126471840)
 (hJ : ∀ y, F 16 y=true → F 17 y=false →
   (flipsTo (F 15) false y ∪ flipsTo (F 18) true y).card≤53874150507309062240)
 (x : ((Fin 5591 × Bool) × I) → Bool) :
 let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (3:Fin 4)).stage F
 parent S F 8 x=true → parent S F 9 x=false →
 (flipsTo (parent S F 7) false x ∪ flipsTo (parent S F 12) true x).card≤111465855403106917280 := by sorry
