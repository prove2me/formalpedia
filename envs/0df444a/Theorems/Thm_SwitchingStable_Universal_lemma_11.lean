-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_11
-- name    : SwitchingStable.Universal.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:27.966179+00:00
-- url     : https://prove2.me/theorems/c48449a2-a8c7-45c8-9bdb-86c9b75449e2
-- title:
--   Lemma 11 — Second-boundary witnesses and disjoint exceptions
-- statement:
--   In the promoted market every $F_a$ occurrence has a second-boundary witness outside its coordinate and first two owners. A $C_0$ occurrence has its second boundary supplied by the endpoint, has such an outside witness, or belongs to the actual exceptional class $\mathcal B_C$. For its count $b_C$,
--   $$b_C\le c,\qquad b_C+f_a\le r_1.$$
--   The exceptional three-cycle map is injective into $R_1$ and its image is disjoint from the two-person swap image of $F_a$. These assertions retain both witness alternatives and the disjointness needed for the count bound.
--
--   Differences from the source:
--   - encoding: The exceptional case in the proof, where the next partner after the three-cycle is w0 → Exceptional is computed from that three-cycle and next-partner test; endpoint means fewer than two future partners; reason: This fixes the actual exceptional class and both source maps, rather than choosing a set to make the inequalities hold.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 7, PDF p. 8, Lemma 11

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_11 {n : ℕ} (I : StableMatching.Instance n) (hI : StablePartnersFirst I) (ε : Direction) :
    (∀ (μ : StableMatching.Matching n) (u : Fin n), I.IsStable μ → Fa I μ ε u →
      ∃ h, Additional I μ ε u h 2) ∧
    (∀ (μ : StableMatching.Matching n) (u : Fin n), I.IsStable μ → C0 I μ ε u →
      distance I μ u ε < 2 ∨ (∃ h, Additional I μ ε u h 2) ∨ Exceptional I μ ε u) ∧
    (let v := occurrenceCounts I ε; v.bC ≤ v.c ∧ v.bC+v.fa ≤ v.r1) ∧
    (∀ (μ : StableMatching.Matching n) (u : Fin n), I.IsStable μ → Exceptional I μ ε u →
      I.IsStable (swapThree I μ ε u) ∧ R1 I (swapThree I μ ε u) ε u) ∧
    Set.InjOn (fun o : StableMatching.Matching n × Fin n => (swapThree I o.1 ε o.2, o.2))
      {o | I.IsStable o.1 ∧ Exceptional I o.1 ε o.2} ∧
    (∀ (μ ν : StableMatching.Matching n) (u h : Fin n), I.IsStable μ → I.IsStable ν →
      Exceptional I μ ε u → Fa I ν ε h → (swapThree I μ ε u, u) ≠ (swap I ν ε h, h)) := by sorry

end SwitchingStable.Universal
