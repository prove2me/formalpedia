-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_2_6
-- name    : SunMinCut.Cactus.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:23:58.827797+00:00
-- url     : https://prove2.me/theorems/626d2cdd-87a1-4274-a816-d7a34966346f
-- title:
--   Lemma 2.6 — many completed forests
-- statement:
--   Let $G$ be a connected aggregated graph on $n\ge2$ vertices with positive capacities and $c_0$ the capacity of an actual cut with $\lambda\le c_0<9\lambda/4$; let $q_e=\min(w_e,c_0)/c_0$ and $\rho=\sigma(G)/c_0$. Give each support pair $e$ an independent rate-$q_e$ Poisson process, assign the arrivals chronologically to first-fit forests, and let $R(t)$ be the number of complete layers at time $t$. For $0<\gamma<1$, integer $A\ge1$ and $t\ge0$,
--   $$P(R(t)<A)\le(n-1)\exp\bigl(-(1-\gamma)\rho t+(A-1)\log(1/\gamma)\bigr).$$
--   In particular, for $A=\lceil3\rho t/4\rceil$, $P(R(t)<A)\le(n-1)e^{-\rho t/32}$ for every $t\ge0$.
--
--   Differences from the source:
--   - encoding: independent rate-q_e Poisson processes on the support pairs → arrival times built from independent uniforms U as partial sums of −log U/q_e, under the product uniform measure; reason: these are independent exponential waiting times, so the arrival processes have exactly the stated law
--   - encoding: "with probability at least p" → the (outer) product-uniform measure of the failure set of draw tapes is at most 1 − p; reason: implies the probability statement for the measurable success event and needs no measurability side condition
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma 2.6, p. 9

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_Processes

open MeasureTheory

namespace SunMinCut.Cactus

/-- **Lemma 2.6 (Many completed forests)**, Sun 2026, doi:10.5281/zenodo.23915020, p. 9: each
support pair `e` receives an independent rate-`q_e` Poisson process and the arrivals are assigned
to first-fit forests. For `0 < γ < 1`, integer `A ≥ 1` and `t ≥ 0`,
`P(R(t) < A) ≤ (n − 1) exp(−(1 − γ)ρt + (A − 1) log(1/γ))`; in particular, for
`A = ⌈3ρt/4⌉`, `P(R(t) < A) ≤ (n − 1)e^{−ρt/32}`. -/
theorem lemma_2_6 (n m : ℕ) (hn : 2 ≤ n) (G : Graph n m) (hpos : Positive G)
    (hconn : Connected G) (hagg : Aggregated G) (c0 : ℝ) (hc0 : CoarseCut G c0) :
    (∀ γ : ℝ, 0 < γ → γ < 1 → ∀ A : ℕ, 1 ≤ A → ∀ t : ℝ, 0 ≤ t →
      arrivalMeasure m {U | completeAt G c0 U t < A} ≤
        ENNReal.ofReal (((n : ℝ) - 1) *
          Real.exp (-(1 - γ) * rho G c0 * t + ((A : ℝ) - 1) * Real.log (1 / γ)))) ∧
    ∀ t : ℝ, 0 ≤ t →
      arrivalMeasure m {U | completeAt G c0 U t < ⌈3 * rho G c0 * t / 4⌉₊} ≤
        ENNReal.ofReal (((n : ℝ) - 1) * Real.exp (-(rho G c0 * t / 32))) := by sorry

end SunMinCut.Cactus
