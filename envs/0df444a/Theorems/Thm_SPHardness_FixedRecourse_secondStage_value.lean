-- Prove2me | Theorems.Thm_SPHardness_FixedRecourse_secondStage_value
-- name    : SPHardness.FixedRecourse.secondStage_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:39.660974+00:00
-- url     : https://prove2.me/theorems/0950c19f-11dc-415b-9071-6e52b24cfbe3
-- title:
--   Value of problem (2), proof of Lemma 2, p. 6
-- statement:
--   Let $\alpha\in\mathbb R^k_+$, $\beta\in\mathbb R$ and $\xi\in[0,1]^k$. The optimal value of the second-stage linear program (2) is
--   $$Q(\xi;\alpha,\beta)=\max\{\sum_j\alpha_j\xi_j-\beta,0\}.$$
--   This pointwise identity connects the linear program to the hinge function used in Lemma 2 and Proposition 1.
--
--   **Formalization Note** The claim is about the value. The page's assertion of unique optimal decisions fails at ties and zero coordinates.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 6, proof of Lemma 2; also p. 3, proof of Proposition 1

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

theorem secondStage_value {k : ℕ} (α : Fin k → ℝ) (β : ℝ)
    (hα : ∀ j, 0 ≤ α j) (ξ : Fin k → ℝ) (hξ : ξ ∈ cube k) :
    secondStageValue α β ξ = max ((∑ j, α j * ξ j) - β) 0 := by sorry
end SPHardness.FixedRecourse
