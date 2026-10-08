-- Prove2me | Theorems.Thm_WaitJudge_Generic_moment_conditions
-- name    : WaitJudge.Generic.moment_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:11:10.157769+00:00
-- url     : https://prove2.me/theorems/959db3c1-c9f8-4f71-971c-11d55e1c681b
-- title:
--   Sect. 7.1, p. 25 — moment equations for all sample sizes
-- statement:
--   For every generic scenario program satisfying Assumptions 1–2 and the stated measurability convention, the generalized distribution measures F_k obey, for every nonnegative integer m,
--
--   $$
--   \sum_{k=0}^{m}{m\choose k}\int_{[0,1]}(1-v)^{m-k}\,dF_k(v)=1.
--   $$
--
--   These equations express the total probability of all support counts and constrain the infinite family F_0,F_1,… used in the primal moment problem.
--
--   **Formalization Note** The paper's Stieltjes integral is represented by integration against F_k. The sample size m includes zero. The hypotheses include Assumptions 1–2 and the three measurability pins.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 25, Sect. 7.1, display before (34)

import Mathlib
import Definitions.Def_WaitJudge_Generic_Setting

namespace WaitJudge.Generic

open MeasureTheory

theorem moment_conditions
    {S Δ : Type*} [Nonempty S] [MeasurableSpace S] [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S)
    {p : ℕ} (tb : Fin p → S → ℝ)
    (hA1 : Assumption1 f X Xδ tb)
    (hA2 : Assumption2 f X Xδ tb P)
    (hmeas : MeasurabilityPins f X Xδ tb) :
    ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) *
      ∫ v in Set.Icc (0 : ℝ) 1, (1 - v) ^ (m - k) ∂(Fk f X Xδ tb P k) =
      1 := by sorry

end WaitJudge.Generic
