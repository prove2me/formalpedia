-- Prove2me | Theorems.Thm_SqrtAgreement_SRA_agree_ge_sq
-- name    : SqrtAgreement.SRA.agree_ge_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:45.033224+00:00
-- url     : https://prove2.me/theorems/b7c6c9cb-b4d9-46c4-8255-cb077448ca10
-- title:
--   Proof of Theorem 1, p. 48 — in an α-separated model every answer has agreement probability g(y) ≥ α²
-- statement:
--   Let $(P_X,\mathbf p)$ be a generating model on finite sets $\mathcal X$ and $\mathcal Y$, and write $g(y)=\sum_{x\in\mathcal X}P_X(x)p_y(x)^2$ for the probability that two agents performing the same task both observe $y$. If the model is $\alpha$-separated for some $\alpha>0$, i.e. $\delta(P_X,\mathbf p)\ge\alpha$, then
--   $$g(y)\ \ge\ \alpha^2\qquad\text{for every }y\in\mathcal Y.$$
--
--   This lower bound keeps every agreement probability away from $0$ uniformly over all $\alpha$-separated models, which is what makes the payments $e_j(y)=K/\sqrt{\bar f_j(y)}$ concentrate.
--
--   **Formalization Note** The page derives the strict form $g(y)>\alpha^2$ from "$\delta(P_X,\mathbf p)>\alpha$"; under Definition 5 ($\delta\ge\alpha$) the conclusion is $g(y)\ge\alpha^2$, which is what the subsequent steps use. Since $\delta$ is $0$ when $|\mathcal Y|<2$, the hypothesis forces $|\mathcal Y|\ge 2$.
-- source:
--   Kamble, Shah, Marn, Parekh & Ramchandran, The Square Root Agreement Rule for Incentivizing Truthful Feedback on Online Platforms, arXiv:1507.07045v5, p. 48, proof of Theorem 1 (with the proof of Proposition 4.1)

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

namespace SqrtAgreement.SRA

theorem agree_ge_sq {m k : ℕ} (G : GenModel m k) (α : ℝ) (hG : G.Valid) (hα : 0 < α)
    (hsep : G.AlphaSeparated α) : ∀ y : Fin k, α ^ 2 ≤ G.agree y := by sorry

end SqrtAgreement.SRA
