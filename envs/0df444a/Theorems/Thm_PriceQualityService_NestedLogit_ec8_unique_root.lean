-- Prove2me | Theorems.Thm_PriceQualityService_NestedLogit_ec8_unique_root
-- name    : PriceQualityService.NestedLogit.ec8_unique_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:32:27.311548+00:00
-- url     : https://prove2.me/theorems/5fdf43ab-6cfb-42fd-8229-3fb915086c4d
-- title:
--   (EC.8), Online Supplement p. 6 — the right-hand side is strictly decreasing in $r$, so $r=F(\mathbf q,r)$ has a unique root
-- statement:
--   Consider the two-stage nested logit model with $\mu_1\ge 1$ and $c_{xi}>0$, fix a quality vector $\mathbf q$, and let
--   $$
--   F(\mathbf q,r)=\sum_{x\in\{s,l\}}\mu_1\Bigl(\sum_{j=1}^{m_x}\exp\bigl(\alpha_{xj}q_{xj}-c_{xj}q_{xj}^2-t_x(a_{xj}-b_{xj}q_{xj})+t_xs_{xj}-r-\mu_1\bigr)\Bigr)^{1/\mu_1}.
--   $$
--   1. If at least one nest is nonempty, $r\mapsto F(\mathbf q,r)$ is strictly decreasing on $\mathbb R$.
--   2. The equation
--   $$
--   r=F(\mathbf q,r)
--   $$
--   has exactly one real solution.
--
--   Applied to $\mathbf q=\mathbf q^\dagger$ this is (EC.8): the optimal profit $r^\dagger$ of Theorem 4 is well defined as the unique root.
--
--   **Formalization Note.** The statement is given for every quality vector $\mathbf q$, of which (EC.8) is the case $\mathbf q=\mathbf q^\dagger$. When both nests are empty, $F\equiv 0$ and the unique root is $r=0$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 6 (PDF p. 39), proof of Theorem 4, (EC.8)

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_Optimum

namespace PriceQualityService.NestedLogit

/-- (EC.8), Online Supplement p. 6 (proof of Theorem 4): for every quality vector `q`, the
right-hand side `r ↦ ∑_x μ₁ (∑_j exp(… + t_x s_xj − r − μ₁))^{1/μ₁}` is strictly decreasing in `r`
as soon as some nest is nonempty, and the equation `r = ∑_x μ₁ (…)^{1/μ₁}` has exactly one real
solution (if both nests are empty the right-hand side is `0` and the solution is `r = 0`). -/
theorem ec8_unique_root (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i) (q : Vec M) :
    ((0 < M.m Nest.s ∨ 0 < M.m Nest.l) → StrictAnti (fun r : ℝ => fixedPointRHS M q r)) ∧
      ∃! r : ℝ, r = fixedPointRHS M q r := by sorry

end PriceQualityService.NestedLogit
