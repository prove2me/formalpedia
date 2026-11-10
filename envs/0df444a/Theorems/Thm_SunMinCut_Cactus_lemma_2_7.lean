-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_2_7
-- name    : SunMinCut.Cactus.lemma_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:24:05.200527+00:00
-- url     : https://prove2.me/theorems/6b58eff4-c6b6-482d-aa7e-614bc694b9e9
-- title:
--   Lemma 2.7 — t/72 of the first t forests cross a minimum cut at most twice
-- statement:
--   In the setting of Lemma 2.6 ($G$ connected, aggregated, positive capacities, $n\ge2$, $c_0$ an actual cut capacity with $\lambda\le c_0<9\lambda/4$, rates $q_e$, $\rho=\sigma/c_0$), fix a minimum cut $C$ and an integer $t\ge1$. Except with probability $(n-1)e^{-\rho t/32}+e^{-\rho t/264}$, at least $t/72$ of the first $t$ forests $B_1,\dots,B_t$ built from the arrivals up to time $t$ are spanning trees crossing $C$ at most twice.
--
--   Differences from the source:
--   - encoding: independent rate-q_e Poisson processes on the support pairs → arrival times built from independent uniforms U as partial sums of −log U/q_e, under the product uniform measure; reason: these are independent exponential waiting times, so the arrival processes have exactly the stated law
--   - encoding: "with probability at least p" → the (outer) product-uniform measure of the failure set of draw tapes is at most 1 − p; reason: implies the probability statement for the measurable success event and needs no measurability side condition
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma 2.7, p. 10

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_Processes

open MeasureTheory

namespace SunMinCut.Cactus

/-- **Lemma 2.7**, Sun 2026, doi:10.5281/zenodo.23915020, p. 10: fix a minimum cut `C` and an
integer `t ≥ 1`. Except with probability `(n − 1)e^{−ρt/32} + e^{−ρt/264}`, at least `t/72` of
the first `t` forests (built from the Poisson arrivals up to time `t`) are spanning trees crossing
`C` at most twice. -/
theorem lemma_2_7 (n m : ℕ) (hn : 2 ≤ n) (G : Graph n m) (hpos : Positive G)
    (hconn : Connected G) (hagg : Aggregated G) (c0 : ℝ) (hc0 : CoarseCut G c0)
    (S : Finset (Fin n)) (hS : IsMinCut G S) (t : ℕ) (ht : 1 ≤ t) :
    arrivalMeasure m {U | ¬ ((t : ℝ) / 72 ≤ goodLayers (stream G c0 U t) t S)} ≤
      ENNReal.ofReal (((n : ℝ) - 1) * Real.exp (-(rho G c0 * t / 32)) +
        Real.exp (-(rho G c0 * t / 264))) := by sorry

end SunMinCut.Cactus
