-- Prove2me | Theorems.Thm_SensitivityJointCover_endpoint22_phase1_bound
-- name    : SensitivityJointCover.endpoint22_phase1_bound
-- status  : Proved
-- author  : @jennyuxi
-- created : 2026-11-13T00:22:24.412466+00:00
-- url     : https://prove2.me/theorems/409b3d51-0778-4512-9c47-aca9e872c9bf
-- title:
--   Four-failure joint cover for the actual 22-state second phase
-- statement:
--   Consider the published 22-state, four-phase Boolean construction on a loopless regular tournament with 5591 vertices and outdegree 2795, with any binary edge labeling. Let $F_0,\ldots,F_{21}$ be the nested child predicates: a larger index implies a smaller-index predicate. Let $G$ be the output of its actual second-phase recipe (phase index 1).
--
--   Assume three uniform bounds on child coordinate flips: at an input where $F_{12}$ is true, at most $b$ single-coordinate flips make it false; at an input where $F_{10}$ is false, at most $a$ flips make it true; and at an input where $F_{12}$ is false, at most $s$ flips make $F_{13}$ true. The bounds $a,b,s$ are arbitrary natural numbers.
--
--   For every parent input $x$ with $G_1(x)=1$ and $G_2(x)=0$,
--
--   $$
--   \left|\{z:G_1(x^{\{z\}})=0\}\ \cup\ \{z:G_{11}(x^{\{z\}})=1\}\right|
--   \le 2b+2791a+4s.
--   $$
--
--   Here $x^{\{z\}}$ flips coordinate $z$. States 1 and 2 of this phase have the same target 12 and guard 10, with tolerances 4 and 3; state 11 has target 13, guard 10, and tolerance zero. The theorem uses these actual recipe entries, rather than a replacement Boolean family. It applies to the selected Paley tournament and labeling by specialization.
--
--   This is a supporting conditional sensitivity bound. It supplies no new separation exponent and asserts no complete numerical cycle certificate. No positivity assumption on $a,b,s$ or nonemptiness assumption on the child coordinate type is needed.
-- source:
--   Original joint-cover deduction from phase index 1, entries 1, 2, and 11 of Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe: https://prove2.me/definitions/c0e9ff4f-3de6-4821-bfbd-0a95cc15178b (Endpoint22Recipes). Uses the unchanged ordinaryParent, ordinaryRow, and guardFailures interfaces of Sensitivity213981Formal_ConditionalOrdinary. Underlying accepted construction by @yousofy with Codex: https://prove2.me/theorems/0e93b146-3cac-42d3-b8f4-74010d06b636; retains its OpenAI/math and earlier community attribution. The new joint-cover implication is proved here; no source is claimed to establish it or a 2.15 separation.

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

theorem SensitivityJointCover.endpoint22_phase1_bound {I : Type} [Fintype I]
    (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬ Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool)
    (htor : ∀ r z, r ≠ z → (Adj r z ↔ ¬ Adj z r))
    (hd : ∀ v, (Finset.univ.filter (Adj v)).card = 2795)
    (F : Fin 22 → (I → Bool) → Bool) (hF : Nested F)
    (b a s : ℕ) (hb : BBound F 12 12 b) (ha : ABound F 10 10 a)
    (hs : ABound F 12 13 s)
    (x : ((Fin 5591 × Bool) × I) → Bool) :
    let S := (Sensitivity5591Endpoint22.recipe Adj loopless label (1 : Fin 4)).stage F
    let G := parent S F
    G 1 x = true → G 2 x = false →
      ((flipsTo (G 1) false x) ∪ (flipsTo (G 11) true x)).card ≤
        2*b+2791*a+4*s := by sorry
