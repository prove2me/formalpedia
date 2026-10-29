-- Prove2me | Theorems.Thm_PutermanMDP_SemiMarkov_finite_evaluation
-- name    : PutermanMDP.SemiMarkov.finite_evaluation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:32.448979+00:00
-- url     : https://prove2.me/theorems/54a02fef-4727-4a10-bd71-facc6a7e2543
-- title:
--   Theorem 11.4.3 — finite-state semi-Markov evaluation equation
-- statement:
--   Let $S$ be finite and nonempty. Fix a stationary randomized rule $d$ whose embedded transition matrix $M_d$ is unichain, in the semi-Markov model with Assumption 11.1.1. Let $M_d^*$ be its Cesaro limiting matrix and define
--   $$H_d=(I-M_d+M_d^*)^{-1}(I-M_d^*),\qquad h^{d^\infty}=H_d(r_d-g^{d^\infty}y_d).$$
--   Then the ratio-average gain is a real constant independent of the initial state, and the constructed gain and bias satisfy
--   $$h^{d^\infty}=r_d-g^{d^\infty}y_d+M_dh^{d^\infty}.$$
--   This gives the finite-state policy evaluation equation with the source's specific deviation-matrix bias. It is the goal of this scoped mission.
--
--   **Formalization Note** Nonexplosion is the chapter's standing Assumption 11.1.1. Finite means and absolutely summable action mixtures make the single-transition reward and time data real. There is no finite-action assumption: stationary randomized rules may have countably supported distributions on arbitrary nonempty action types. The gain is defined from expected rewards and holding times, and its real-valuedness is a conclusion, not an instance field.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, https://doi.org/10.1002/9780470316887, p. 552 (PDF 568), Theorem 11.4.3

import Definitions.Def_PutermanMDP_SemiMarkov_Deviation

namespace PutermanMDP.SemiMarkov

theorem finite_evaluation {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : Model S) (d : Rule M) (hNE : Nonexplosive M) (hU : Unichain M d) :
    let P : Matrix S S ℝ := transitionMatrix M d
    let Pstar : Matrix S S ℝ := cesaroMatrix M d
    let H : Matrix S S ℝ := (1 - P + Pstar)⁻¹ * (1 - Pstar)
    let g : S → ℝ := fun s => (gain M d s).toReal
    let h : S → ℝ := H.mulVec (fun s => ruleReward M d s - g s * ruleTime M d s)
    (∃ scalar : ℝ, ∀ s, gain M d s = (scalar : EReal)) ∧
    ∀ s, h s = ruleReward M d s - g s * ruleTime M d s + ∑ j, P s j * h j := by sorry

end PutermanMDP.SemiMarkov
