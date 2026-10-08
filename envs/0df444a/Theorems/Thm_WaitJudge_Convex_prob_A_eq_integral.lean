-- Prove2me | Theorems.Thm_WaitJudge_Convex_prob_A_eq_integral
-- name    : WaitJudge.Convex.prob_A_eq_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:59:07.474582+00:00
-- url     : https://prove2.me/theorems/2f437e41-11f0-422b-9d4a-a14dcf732486
-- title:
--   (16), Sect. 5.1.1, p. 14 — ℙᴺ{A} = ∫_(ε(k),1] (1−v)^(N−k) dF_k(v)
-- statement:
--   Let $\mathbb P$ be a probability measure, let Assumptions 1 and 2 and the measurability conditions hold, and fix $k\le N$ and a threshold $\epsilon(k)$. For the event
--   $$A=\{V(x^*_N)>\epsilon(k)\ \wedge\ s^*_N=k\ \wedge\ \text{the first $k$ constraints are of support}\}$$
--   of (15),
--   $$\mathbb P^N\{A\}=\int_{(\epsilon(k),1]}(1-v)^{N-k}\,\mathrm dF_k(v),$$
--   where $F_k(v)=\mathbb P^k\{V(x^*_k)\le v\wedge s^*_k=k\}$ is the generalized distribution function (12).
--
--   Given $V(x^*_k)=v$, the probability that the other $N-k$ independent constraints are all satisfied by $x^*_k$ is $(1-v)^{N-k}$; combined with $A=B$ almost surely, this gives the formula.
--
--   **Formalization Note** $F_k$ is the (non-normalised) finite measure on $\mathbb R$ whose distribution function is $F_k$, and the integral is the Lebesgue integral over $(\epsilon(k),1]$ against it. The probability is an extended nonnegative real, compared with the real integral through $\mathrm{ofReal}$.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 14, Sect. 5.1.1, (16) (with (12), p. 13)

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization

namespace WaitJudge.Convex

theorem prob_A_eq_integral {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hA1 : Assumption1 c X Xδ tb) (hA2 : Assumption2 c X Xδ tb P)
    (hmeas : MeasurabilityPins c X Xδ tb)
    (ε : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    (Measure.pi fun _ : Fin N => P) {ω | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k ∧
        ∀ i : Fin N, i.val < k → i ∈ supportSet c X Xδ tb ω} =
      ENNReal.ofReal (∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(Fk P c X Xδ tb k)) := by sorry

end WaitJudge.Convex
