-- Prove2me | Theorems.Thm_UnderstandingML_stumps_weakly_learn_three_piece
-- name    : UnderstandingML.stumps_weakly_learn_three_piece
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:59:26.188596+00:00
-- url     : https://prove2.me/theorems/ecd0d724-7944-4472-b710-265fc16feb2f
-- title:
--   Example 10.1: ERM over decision stumps is a 1/12-weak learner for the class of 3-piece classifiers over ℝ
-- statement:
--   **Example 10.1 (Weak Learning of 3-Piece Classifiers Using Decision Stumps).** Let $X = \mathbb{R}$ and let $H$ be the class of 3-piece classifiers $h_{\theta_1,\theta_2,b}$ ($\theta_1 < \theta_2$, $b \in \{\pm1\}$), equal to $b$ on $x < \theta_1$ or $x > \theta_2$ and to $-b$ on $[\theta_1, \theta_2]$. Let $B$ be the class of decision stumps $\{x \mapsto \operatorname{sign}(x - \theta)\cdot b\}$. Then $ERM_B$ is a γ-weak learner for $H$, for $\gamma = 1/12$: for every distribution consistent with $H$ there is a decision stump with $L_D(h) \le 1/3$, and since $\mathrm{VCdim}(B) = 2$, with enough examples $ERM_B$ returns with probability at least $1-\delta$ a hypothesis with error at most $1/3 + 1/12 = 1/2 - 1/12$.
--
--   Formally: there is one sample-size function $m_H$ such that every ERM learner over the decision stumps is a $1/12$-weak learner for the 3-piece classifiers with $m_H$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §10.1 Example 10.1 pp. 132-133

import Definitions.Def_UnderstandingML_Boosting

open MeasureTheory

namespace UnderstandingML

/-- **Example 10.1** (pp. 132–133). Let `X = ℝ`, `H` the class of 3-piece classifiers and `B`
the class of decision stumps. Then `ERM_B` is a γ-weak learner for `H` with `γ = 1/12`: for
every distribution consistent with `H` some decision stump has error at most `1/3`, and since
`VCdim(B) = 2`, with enough examples the `ERM_B` rule returns, with probability at least
`1 − δ`, a hypothesis with error at most `1/3 + 1/12 = 1/2 − 1/12`. Stated for every ERM
learner over the stumps, with one sample-size function. -/
theorem stumps_weakly_learn_three_piece :
    ∃ mH : ℝ → ℕ, ∀ A : Learner (ℝ × Bool) (ℝ → Bool), IsERMLearner loss01 decisionStumps A →
      IsWeakLearnerWith threePieceClassifiers (1 / 12) A mH := by sorry

end UnderstandingML
