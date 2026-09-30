-- Prove2me | Theorems.Thm_UnderstandingML_linear_regression_not_learnable
-- name    : UnderstandingML.linear_regression_not_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:15:01.039054+00:00
-- url     : https://prove2.me/theorems/cd9972c5-7f35-4cce-8a83-7478a86a14c0
-- title:
--   Examples 12.8–12.9: linear regression on ℝ with the squared loss is not (agnostic) PAC learnable, neither over H = ℝ nor over H = [−1, 1]
-- statement:
--   **Example 12.8 (Nonlearnability of Linear Regression Even If $d = 1$).** Let $H = \mathbb{R}$ and the loss be the squared loss $\ell(w,(x,y)) = (wx - y)^2$. For every deterministic algorithm $A$ there is a distribution on which $A$ fails; the problem is not PAC learnable. **Example 12.9.** The same holds for the bounded convex class $H = \{w : |w| \le 1\}$.
--
--   Formally: `AgnosticPACLearnable squaredLoss1 H` fails for $H = \mathbb{R}$ and for $H = [-1, 1]$ (the learners of Definition 3.4 are deterministic).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §12.2.1 pp. 164-166, Examples 12.8 and 12.9 with their proofs

import Definitions.Def_UnderstandingML_Convex

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Examples 12.8–12.9** (pp. 164–166): nonlearnability of linear regression even if `d = 1`.
With `H = ℝ` and the squared loss `ℓ(w, (x, y)) = (wx − y)²`, the problem is not (agnostic) PAC
learnable; and neither is it with the bounded convex class `H = {w : |w| ≤ 1}`. (The learners of
Definition 3.4 are deterministic, as the book assumes.) -/
theorem linear_regression_not_learnable :
    ¬ AgnosticPACLearnable squaredLoss1 (Set.univ : Set ℝ) ∧
    ¬ AgnosticPACLearnable squaredLoss1 (Set.Icc (-1 : ℝ) 1) := by sorry

end UnderstandingML
