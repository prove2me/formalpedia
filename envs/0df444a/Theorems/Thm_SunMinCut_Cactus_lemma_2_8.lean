-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_2_8
-- name    : SunMinCut.Cactus.lemma_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:24:16.411406+00:00
-- url     : https://prove2.me/theorems/a01d3e73-5a70-4420-8008-5cd13d9a2918
-- title:
--   Lemma 2.8 — covering all minimum cuts
-- statement:
--   In the setting of Lemma 2.6, consider the uncapped Poisson construction with exact forest computations at horizon $t$: the first at most $t$ complete source trees $T_j=B_j$, $1\le j\le\min(R(t),t)$, each with one independent local search, i.e. its auxiliary multigraph $G_{T_j}$ (each record sampled independently with probability $p_e=\min\{w_e,d_0(T_j)\}/(2d_0(T_j))$, plus a copy of every tree edge) and the cactus of its three-edge-connected components, which represents the bridges and two-edge bonds of $G_{T_j}$. For each fixed minimum cut $C$ of $G$, the probability that none of the retained auxiliary cacti represents $C$ is at most $(n+1)e^{-t/1440}$. Thus the probability of failing to cover every minimum cut is at most $\binom n2(n+1)e^{-t/1440}$.
--
--   Differences from the source:
--   - encoding: independent rate-q_e Poisson processes on the support pairs → arrival times built from independent uniforms U as partial sums of −log U/q_e, under the product uniform measure; reason: these are independent exponential waiting times, so the arrival processes have exactly the stated law
--   - encoding: "with probability at least p" → the (outer) product-uniform measure of the failure set of draw tapes is at most 1 − p; reason: implies the probability statement for the measurable success event and needs no measurability side condition
--   - encoding: "represented by the retained auxiliary cactus" → the cut is a bridge or a two-edge bond (at most two crossing edges, both shores connected) of the auxiliary multigraph; reason: this is the family the contracted cactus represents, as stated on p. 7
--   - generalization: the integer horizon t chosen in (6) → every natural horizon t, including zero; reason: the same bounds hold for every positive integer horizon; at zero both right sides are at least one, and specializing to (6) recovers the entire printed claim
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma 2.8, p. 11

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_Processes

open MeasureTheory

namespace SunMinCut.Cactus

/-- **Lemma 2.8 (Covering all minimum cuts)**, Sun 2026, doi:10.5281/zenodo.23915020, p. 11: for
the uncapped Poisson construction with exact forest computations (horizon `t`, at most the first
`t` complete source trees, one independent local search on each), and each fixed original
minimum cut `C`, the probability that none of the retained auxiliary cacti represents `C` is at
most `(n + 1)e^{−t/1440}`; the probability of failing to cover every minimum cut is at most
`(n choose 2)(n + 1)e^{−t/1440}`. -/
theorem lemma_2_8 (n m : ℕ) (hn : 2 ≤ n) (G : Graph n m) (hpos : Positive G)
    (hconn : Connected G) (hagg : Aggregated G) (c0 : ℝ) (hc0 : CoarseCut G c0) (t : ℕ) :
    (∀ S : Finset (Fin n), IsMinCut G S →
      coverMeasure m {ω | ¬ Covered G c0 ω t S} ≤
        ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (-((t : ℝ) / 1440)))) ∧
    coverMeasure m {ω | ∃ S : Finset (Fin n), IsMinCut G S ∧ ¬ Covered G c0 ω t S} ≤
      ENNReal.ofReal ((n.choose 2 : ℝ) * ((n : ℝ) + 1) * Real.exp (-((t : ℝ) / 1440))) := by sorry

end SunMinCut.Cactus
