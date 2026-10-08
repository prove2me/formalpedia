-- Prove2me | Theorems.Thm_WaitJudge_Convex_prob_violation_eq_sum_integral
-- name    : WaitJudge.Convex.prob_violation_eq_sum_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:59:24.053318+00:00
-- url     : https://prove2.me/theorems/5b10157d-5c7b-4cba-93d8-a47b1f3a3cc8
-- title:
--   (17), Sect. 5.1.1, p. 14 — ℙᴺ{V(x*_N) > ε(s*_N)} = Σ_k C(N,k) ∫_(ε(k),1] (1−v)^(N−k) dF_k(v)
-- statement:
--   Consider a convex scenario program: $\mathcal X$, every $\mathcal X_\delta$ and the tie-break functions are convex, the sample $\delta^{(1)},\dots,\delta^{(N)}$ is i.i.d. with law $\mathbb P$, $N>d$, and Assumptions 1 and 2 and the measurability conditions hold. Let $\epsilon(k)\in[0,1]$ for $k=0,1,\dots,d$. Then
--   $$\mathbb P^N\{V(x^*_N)>\epsilon(s^*_N)\}=\sum_{k=0}^{d}\binom Nk\int_{(\epsilon(k),1]}(1-v)^{N-k}\,\mathrm dF_k(v),$$
--   where $F_k$ is the generalized distribution function (12).
--
--   This is the formula by which the probability that the violation exceeds the a-posteriori level $\epsilon(s^*_N)$ is computed from $F_0,\dots,F_d$ alone; Theorem 1 is obtained by maximising its right-hand side over all $(F_0,\dots,F_d)$ compatible with convex problems.
--
--   **Formalization Note** $F_k$ is a finite measure on $\mathbb R$, and the probability is compared with the real right-hand side through $\mathrm{ofReal}$.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 14, Sect. 5.1.1, (17) (from (13), (14), (16))

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization

namespace WaitJudge.Convex

theorem prob_violation_eq_sum_integral {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hX : Convex ℝ X) (hXδ : ∀ δ, Convex ℝ (Xδ δ))
    (htb : ∀ j, ConvexOn ℝ Set.univ (tb j))
    (hA1 : Assumption1 c X Xδ tb) (hA2 : Assumption2 c X Xδ tb P)
    (hmeas : MeasurabilityPins c X Xδ tb)
    (N : ℕ) (hN : d < N) (ε : ℕ → ℝ) (hε : ∀ k ≤ d, 0 ≤ ε k ∧ ε k ≤ 1) :
    (Measure.pi fun _ : Fin N => P) {ω | ε (sstar c X Xδ tb ω) < violation P Xδ (xstar c X Xδ tb ω)} =
      ENNReal.ofReal (∑ k ∈ Finset.range (d + 1),
        (N.choose k : ℝ) * ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(Fk P c X Xδ tb k)) := by sorry

end WaitJudge.Convex
