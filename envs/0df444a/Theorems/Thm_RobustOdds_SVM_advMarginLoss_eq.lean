-- Prove2me | Theorems.Thm_RobustOdds_SVM_advMarginLoss_eq
-- name    : RobustOdds.SVM.advMarginLoss_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:41:22.594102+00:00
-- url     : https://prove2.me/theorems/687547d3-21e6-4e73-9909-fabb314b4b58
-- title:
--   Appendix D, p. 18 — adversarial hinge objective in closed form
-- statement:
--   For $\varepsilon\ge0$, let $L_{\mathrm{adv}}(w)$ be the expectation of the largest hinge loss over $\ell_\infty$ perturbations of radius $\varepsilon$, with the maximum taken separately for each input and label. Then
--
--   $$
--   L_{\mathrm{adv}}(w)=\mathbb E_D\!\left[\max\{0,1-yw^\top x+\varepsilon\sum_i|w_i|\}\right].
--   $$
--
--   Thus the adversary contributes the $\ell_1$ norm of the weights. Adding the same quadratic regularizer to both sides gives the objective identity used in the proof of Lemma D.5.
--
--   **Formalization Note** Equation (2) puts the maximum inside expectation. The display in the proof of Lemma D.5 prints it outside; that placement does not yield this identity.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 18, App. D, proof of Lemma D.5, two objective displays

import Mathlib
import Definitions.Def_RobustOdds_SVM_Setting

namespace RobustOdds.SVM

open MeasureTheory

theorem advMarginLoss_eq (d : ℕ) (p η ε : ℝ) (hε : 0 ≤ ε)
    (w : Fin (d + 1) → ℝ) :
    advMarginLoss d p η ε w =
      (1 / 2) * ∫ x, max 0 (1 - ∑ i, w i * x i + ε * ∑ i, |w i|)
        ∂(RobustOdds.Tradeoff.condLaw d p η 1) +
      (1 / 2) * ∫ x, max 0 (1 + ∑ i, w i * x i + ε * ∑ i, |w i|)
        ∂(RobustOdds.Tradeoff.condLaw d p η (-1)) := by sorry

end RobustOdds.SVM
