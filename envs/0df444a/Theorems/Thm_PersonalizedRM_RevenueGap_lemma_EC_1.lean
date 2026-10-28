-- Prove2me | Theorems.Thm_PersonalizedRM_RevenueGap_lemma_EC_1
-- name    : PersonalizedRM.RevenueGap.lemma_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:50.648903+00:00
-- url     : https://prove2.me/theorems/8f787546-def5-4546-ac70-dcd89be8c79a
-- title:
--   Lemma EC.1, p. ec2 — Diag(q) − qqᵀ is PSD with λ_min ≥ min_j q_j · (1 − Σ_j q_j)
-- statement:
--   Let $\iota$ be a finite index set (the offered products) and let $q_j > 0$, $j \in \iota$, be purchase probabilities with $\sum_j q_j < 1$, so that the no-purchase probability $q_0 = 1 - \sum_j q_j$ is positive. Let $m \le q_j$ for every $j$. Then for every vector $u \in \mathbb R^\iota$,
--
--   $$0 \le \sum_j q_j u_j^2 - \Big(\sum_j q_j u_j\Big)^2 \qquad\text{and}\qquad m\, q_0 \sum_j u_j^2 \le \sum_j q_j u_j^2 - \Big(\sum_j q_j u_j\Big)^2 .$$
--
--   The right-hand side is the quadratic form $u^\top(\mathrm{Diag}(q) - qq^\top)u$ of the matrix $A_{i,S_i}$ whose diagonal entries are $q_j(1-q_j)$ and whose off-diagonal entries are $-q_jq_k$. The statement says that this matrix is positive semidefinite and that its smallest eigenvalue is at least $\min_j q_j \cdot q_0$, which is (EC.5) with $q_j = \mathbb P_{z_i}(j; S_i, \theta)$.
--
--   This is the curvature estimate behind the strong convexity of the logit log-likelihood (Lemma 2): the Hessian of $\ell_n$ is an average of block matrices built from $A_{i,S_i}$.
--
--   **Formalization Note.** The eigenvalue bound is stated as the equivalent quadratic-form inequality, for an arbitrary finite index set and arbitrary probabilities with the stated sign constraints; every such vector arises as MNL probabilities, so this is the page's statement. The page's hypothesis $S_i \ne \emptyset$ is not needed in this form.
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), p. ec2, Lemma EC.1, (EC.5)

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

namespace PersonalizedRM.RevenueGap

/-- Lemma EC.1 (p. ec2), quadratic-form version: for probabilities `q j > 0` of the offered
products with `Σ q j < 1` (so the no-purchase probability `q₀ = 1 − Σ q j` is positive), the
matrix `Diag(q) − q qᵀ` is positive semidefinite and its smallest eigenvalue is at least
`min_j q j · q₀`. -/
theorem lemma_EC_1 {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq_pos : ∀ j, 0 < q j)
    (hq_sum : ∑ j, q j < 1) (m : ℝ) (hm : ∀ j, m ≤ q j) (u : ι → ℝ) :
    0 ≤ ∑ j, q j * u j ^ 2 - (∑ j, q j * u j) ^ 2 ∧
      m * (1 - ∑ j, q j) * ∑ j, u j ^ 2 ≤ ∑ j, q j * u j ^ 2 - (∑ j, q j * u j) ^ 2 := by sorry

end PersonalizedRM.RevenueGap
