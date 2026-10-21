-- Prove2me | Theorems.Thm_PartialCompletion_Budget_lambda1_decreasing_n0
-- name    : PartialCompletion.Budget.lambda1_decreasing_n0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:43.969193+00:00
-- url     : https://prove2.me/theorems/d5760879-ee17-42ec-aba2-b714ccf1f929
-- title:
--   Proof of Proposition 3, Online Appendix p. 2 — Λ₁ decreases and n₀ exists
-- statement:
--   On the physical variety domain $n\ge1$, define the first derivative-sign numerator by
--
--   $$
--   \Lambda_1(n)=-n(4n-\theta)g'(n)+\theta g(n).
--   $$
--
--   Under the model's assumptions, $\Lambda_1$ is strictly decreasing. A small-budget variety $n_0$ exists: it equals $1$ when $\Lambda_1(1)\le0$, while for $\Lambda_1(1)>0$ it is a root above $1$.
--
--   This is the appendix's variety characterization for the low-budget regime.
--
--   **Formalization Note** The result is restricted to $n\ge1$; the derivative assumptions on $g$ are likewise restricted there. The source's existence argument uses that the negative derivative grows in magnitude because $g'$ is positive and nondecreasing.
-- source:
--   Zhang, Atasu & Ramachandran, Partial Completion as a Nonprofit Strategy, SSRN 3684891, Online Appendix p. 2 (PDF 35), proof of Proposition 3, Case 1

import Mathlib
import Definitions.Def_PartialCompletion_Budget_Model

namespace PartialCompletion.Budget

theorem lambda1_decreasing_n0 (M : Model) (hM : M.Standing) :
    StrictAntiOn (Λ1 M) (Set.Ici 1) ∧ ∃ n0 : ℝ, IsN0 M n0 := by sorry

end PartialCompletion.Budget
