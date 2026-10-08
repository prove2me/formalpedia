-- Prove2me | Theorems.Thm_WaitJudge_Convex_prob_Sk_eq_choose_mul
-- name    : WaitJudge.Convex.prob_Sk_eq_choose_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:57:50.463051+00:00
-- url     : https://prove2.me/theorems/bcb7c23d-954a-42c2-a79d-bc3614a0f4a3
-- title:
--   (14), Sect. 5.1.1, p. 14 — ℙᴺ{S_k} = C(N,k) ℙᴺ{A} by exchangeability
-- statement:
--   Let $\delta^{(1)},\dots,\delta^{(N)}$ be i.i.d. with law $\mathbb P$, and let the measurability conditions hold. Fix $k\le N$ and a threshold $\epsilon(k)$. Let
--   $$S_k=\{V(x^*_N)>\epsilon(k)\ \wedge\ s^*_N=k\}$$
--   and let $A\subseteq S_k$ be the event (15) where, in addition, the first $k$ constraints are of support. Then
--   $$\mathbb P^N\{S_k\}=\binom Nk\,\mathbb P^N\{A\}.$$
--
--   The identity groups the samples of $S_k$ by the index set of their $k$ support constraints; the $\binom Nk$ groups have the same probability because the sample is i.i.d. and the solution does not depend on the order of the constraints.
--
--   **Formalization Note** "The first $k$ constraints" are those with indices $0,\dots,k-1$. The measurability hypotheses (joint measurability of $\{(x,\delta):x\in\mathcal X_\delta\}$ and of the solution maps) make both events measurable; the paper takes measurability for granted. No convexity and no Assumption 1 or 2 is needed.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF pp. 13–14, Sect. 5.1.1, (14) and (15)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization

namespace WaitJudge.Convex

theorem prob_Sk_eq_choose_mul {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hmeas : MeasurabilityPins c X Xδ tb) (ε : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    (Measure.pi fun _ : Fin N => P) {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k} =
      ((N.choose k : ℕ) : ENNReal) * (Measure.pi fun _ : Fin N => P)
        {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k ∧
          ∀ i : Fin N, i.val < k → i ∈ supportSet c X Xδ tb ω} := by sorry

end WaitJudge.Convex
