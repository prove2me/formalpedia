-- Prove2me | Theorems.Thm_SensitivityJointCover_endpoint22_phase2_parent_bound
-- name    : SensitivityJointCover.endpoint22_phase2_parent_bound
-- status  : Proved
-- author  : @jennyuxi
-- created : 2026-11-13T05:12:56.412204+00:00
-- url     : https://prove2.me/theorems/42ad170b-0b7b-43cf-b82a-4af016772393
-- title:
--   Parent joint cover for states 14, 19, and 20 of the actual 22-state recipe
-- statement:
--   Consider the published four-phase, 22-state Boolean construction on a loopless tournament with 5591 vertices and outdegree 2795, with any binary edge labels. Let $H_0,\ldots,H_{21}$ be nested Boolean predicates on a finite child-coordinate type. Here nested means that $H_j=1$ implies $H_i=1$ whenever $i\le j$. Let $F$ be the output of the actual second phase (phase index 1) applied to $H$, and let $G$ be the output of the actual third phase (phase index 2) applied to $F$.
--
--   Write $\operatorname{Up}_j(y)$ and $\operatorname{Down}_j(y)$ for single-coordinate flips making predicate $j$ true and false, respectively. Every flip set below is evaluated at its stated input, and its cardinality counts coordinates, not witness rows.
--
--   Assume the following uniform bounds on $H$: if $H_{12}(y)=1$, then $|\operatorname{Down}_{12}(y)|\le53627300001453076$; if $H_{10}(y)=0$, then $|\operatorname{Up}_{10}(y)|\le914422496216727$; and if $H_{12}(y)=0$, then $|\operatorname{Up}_{13}(y)|\le1217719417783$. These are precisely the hypotheses used by the accepted child joint-cover theorem.
--
--   Assume also that $F$ is nested and satisfies the following child-profile bounds: if $F_{17}(y)=1$, then $|\operatorname{Down}_{13}(y)|\le986662590537317840$; if $F_2(y)=0$, then $|\operatorname{Up}_{11}(y)|\le24354388355660$; and if $F_{17}(y)=1$ and $F_{18}(y)=0$, then $|\operatorname{Up}_{18}(y)|\le47117605675757176$.
--
--   Then, for every parent input $x$ with $G_{19}(x)=1$ and $G_{20}(x)=0$,
--
--   $$
--   |\operatorname{Down}_{14}(x)\cup\operatorname{Up}_{20}(x)|\le4700783999961812061.
--   $$
--
--   The bound covers every repair signature, including the maximal two-guard-head case.
--
--   This is a conditional supporting transfer theorem for the actual recipe. Its child-profile hypotheses are explicit; it does not itself verify the complete four-phase numerical certificate or claim a new separation exponent. No nonempty child-coordinate type is assumed.
-- source:
--   Original parent-level joint-cover deduction for phase index 2, entries 14, 19, and 20, of Sensitivity213981Formal.Sensitivity5591Endpoint22.recipe (Endpoint22Recipes): https://prove2.me/definitions/c0e9ff4f-3de6-4821-bfbd-0a95cc15178b. Explicitly applies the accepted child joint-cover theorem https://prove2.me/theorems/409b3d51-0778-4512-9c47-aca9e872c9bf. Fixed child-profile constants from the existing 2.13981 construction https://prove2.me/theorems/0e93b146-3cac-42d3-b8f4-74010d06b636, by @yousofy with Codex, retaining its OpenAI/math and earlier community attribution. The new parent implication is proved here; no source is claimed to establish a new full-cycle certificate or exponent.

import Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Theorems.Thm_SensitivityJointCover_endpoint22_phase1_bound
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Prod
import Lean
open Sensitivity213981Formal Sensitivity213981Formal.ThreeBoundWitness
open Sensitivity213981Formal.ThreeBoundProfiles
open scoped Classical
set_option autoImplicit false

theorem SensitivityJointCover.endpoint22_phase2_parent_bound {K : Type} [Fintype K]
    (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ v, ¬ Adj v v)
    (label : Fin 5591 → Fin 5591 → Bool)
    (htor : ∀ r z, r ≠ z → (Adj r z ↔ ¬ Adj z r))
    (hd : ∀ v, (Finset.univ.filter (Adj v)).card = 2795)
    (H : Fin 22 → (K → Bool) → Bool) (hH : Nested H)
    (hB : BBound H 12 12 53627300001453076)
    (hA : ABound H 10 10 914422496216727)
    (hs : ABound H 12 13 1217719417783) :
    let F := parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (1 : Fin 4)).stage H) H
    let G := parent ((Sensitivity5591Endpoint22.recipe Adj loopless label (2 : Fin 4)).stage F) F
    Nested F → BBound F 13 17 986662590537317840 →
    ABound F 2 11 24354388355660 →
    (∀ y, F 17 y = true → F 18 y = false →
      (flipsTo (F 18) true y).card ≤ 47117605675757176) →
    ∀ x, G 19 x = true → G 20 x = false →
      (flipsTo (G 14) false x ∪ flipsTo (G 20) true x).card ≤ 4700783999961812061 := by sorry
