-- Prove2me | Theorems.Thm_WaitJudge_Generic_theorem_3
-- name    : WaitJudge.Generic.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:11:38.839978+00:00
-- url     : https://prove2.me/theorems/abfcd4dd-2dc8-470c-a40a-e57e947a56e5
-- title:
--   Theorem 3, p. 22 — generic wait-and-judge bound by γ*
-- statement:
--   Let S be an arbitrary decision set with real cost f, domain X, and scenario constraints X_δ indexed by a probability space (Δ,ℱ,P). For N≥1 independent samples, let x*_N be the unique tie-broken solution, s*_N its number of support constraints, and V(x*_N) the probability that a new constraint rejects it. Assume existence and uniqueness for every finite sample (Assumption 1), and that almost surely the support constraints alone select the same solution (Assumption 2). For any ε(k)∈[0,1], 0≤k≤N,
--
--   $$
--   \mathbb P^N\{V(x^*_N)>\varepsilon(s^*_N)\}\le\gamma^*,
--   $$
--
--   where γ* is the infimum of q(1) over degree-at-most-N polynomials satisfying the derivative inequalities (31). The bound adapts to the observed number of support constraints without an a priori dimension bound.
--
--   **Formalization Note** The source prints k=0,…,d in Theorem 3, although its generic section has no d; (31) and the preceding paragraph use k=0,…,N, which is the range formalized here. The finite tie-break list pins down the page's tie-break rule. Joint constraint measurability, solution-map measurability, and support-event measurability make explicit the convention of footnote 1. A `Nonempty S` instance is redundant with Assumption 1 and supplies the selector's unused fallback. The probability is compared in extended nonnegative reals with `ENNReal.ofReal γ*`.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 22, Theorem 3 and (31)

import Mathlib
import Definitions.Def_WaitJudge_Generic_Setting

namespace WaitJudge.Generic

open MeasureTheory

theorem theorem_3
    {S Δ : Type*} [Nonempty S] [MeasurableSpace S] [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S)
    {p : ℕ} (tb : Fin p → S → ℝ)
    (hA1 : Assumption1 f X Xδ tb)
    (hA2 : Assumption2 f X Xδ tb P)
    (hmeas : MeasurabilityPins f X Xδ tb)
    (N : ℕ) (hN : 0 < N) (ε : ℕ → ℝ)
    (hε : ∀ k ≤ N, 0 ≤ ε k ∧ ε k ≤ 1) :
    (Measure.pi fun _ : Fin N => P)
      {ω : Fin N → Δ | ε (sstar f X Xδ tb ω) <
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω)} ≤
      ENNReal.ofReal (gammaStar31 N ε) := by sorry

end WaitJudge.Generic
