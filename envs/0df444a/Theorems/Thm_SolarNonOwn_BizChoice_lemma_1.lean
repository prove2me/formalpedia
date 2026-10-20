-- Prove2me | Theorems.Thm_SolarNonOwn_BizChoice_lemma_1
-- name    : SolarNonOwn.BizChoice.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:10.750913+00:00
-- url     : https://prove2.me/theorems/992b3b5f-8ffe-42b5-b1f9-cb344e09d8b5
-- title:
--   Lemma 1, p. 11 — electricity usage is δ − r under every option
-- statement:
--   Let $\delta$ be a customer's realized demand satiation level and $r$ the retail electricity price. For any sales, lease and PPA prices, and any probability law of realized solar generation whose first moment exists, the unique maximizer of expected gross utility minus monthly cost is the same under all four choices $U,S,L,P$:
--
--   $$q_U^*(\delta)=q_S^*(\delta)=q_L^*(\delta)=q_P^*(\delta)=\delta-r.$$
--
--   Equal optimal usage is what lets the customer's earlier business-model choice reduce to a comparison of expected costs.
--
--   **Formalization Note** The usage choice ranges over the real numbers, as in the paper's unconstrained maximization. Integrability of generation is stated so the expected utility has its ordinary value.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), p. 11, Lemma 1

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_Model

noncomputable section
open MeasureTheory

namespace SolarNonOwn.BizChoice

/-- Lemma 1, p. 11: all four expected-utility problems have the same unique optimum. -/
theorem lemma_1 (prm : Params) (x : Prices) (δ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hn : Integrable id ν) :
    ∀ i : BizOpt,
      let payoff : ℝ → ℝ := fun q => ∫ n, grossUtility q δ - monthlyCost prm x q n i ∂ν
      IsMaxOn payoff Set.univ (δ - prm.r) ∧
      (∀ q : ℝ, payoff q = payoff (δ - prm.r) → q = δ - prm.r) := by sorry

end SolarNonOwn.BizChoice
