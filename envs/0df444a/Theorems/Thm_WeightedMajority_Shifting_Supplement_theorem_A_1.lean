-- Prove2me | Theorems.Thm_WeightedMajority_Shifting_Supplement_theorem_A_1
-- name    : WeightedMajority.Shifting.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T13:02:04.409132+00:00
-- url     : https://prove2.me/theorems/99cb0aed-b57f-468d-aff3-c0872cecb005
-- title:
--   Theorem A.1 — lazy weighted sampling satisfies strong independence
-- statement:
--   Let a binary pool with arbitrary positive initial weights be run with the lazy implementation of WMR: weights update on every trial at $\beta=0$, while the selected member is resampled only initially and immediately after a master mistake. Fresh selections use the current cumulative normalized weights and independent uniform numbers on $[0,1]$. All these choices are jointly independent of the full external sequence. Then the implementation satisfies the strong independence condition:
--
--   $$P[\lambda^j\mid G\vee\sigma(\lambda^0,\ldots,\lambda^{j-1})]=\gamma^j\quad\text{almost surely for every }j<t,$$
--
--   where $G$ contains all external prediction vectors and labels, including future ones, and $\gamma^j$ is the published WMR weighted average. This justifies using the conditional tail theorem for the lazy implementation without assuming independent master predictions.
--
--   **Formalization Note** The source's sampling ratios require positive pre-trial totals almost surely. Exhaustion after the final prediction is allowed, and consistency with a fixed pool member is not assumed.
--
--   Differences from the source:
--   - encoding: independent uniform draws when resampling occurs → jointly independent uniform coins for all finite trials, ignoring unused coins; reason: pre-sampling independent unused randomness preserves the law of every run
--   - reading: normalized cumulative intervals in the implementation → positive pre-trial totals, with arbitrary selection on the null event r=0; reason: normalization is undefined after exhaustion; p. 258 explicitly permits arbitrary selection at r=0
--   - encoding: source trials indexed from 1 and almost-sure equalities → zero-based trials and almost-sure implementation relations; reason: the initial case and the immediately-after-mistake transition are explicit
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), DOI 10.1006/inco.1994.1009, p. 257, Theorem A.1

import Definitions.Def_WeightedMajority_Shifting_Supplement_LazySampling

open MeasureTheory

namespace WeightedMajority.Shifting.Supplement

theorem theorem_A_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (t : ℕ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ)
    (ρ lam r : ℕ → Ω → ℝ) (selected : ℕ → Ω → Fin n)
    (hrun : IsLazyWMRRun P t w1 F x ρ lam r selected) :
    StrongIndependence P t w1 F x ρ lam := by sorry

end WeightedMajority.Shifting.Supplement
