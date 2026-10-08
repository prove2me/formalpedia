-- Prove2me | Theorems.Thm_SparseNLO_CWOpt_lemma_2_5
-- name    : SparseNLO.CWOpt.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:12:21.400562+00:00
-- url     : https://prove2.me/theorems/9c41a855-ab06-4012-9fda-0c4c7b6fc08c
-- title:
--   Lemma 2.5 — every CW-minimum of (P) is a basic feasible vector
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and bounded below (Assumption 1), and let $0<s<n$ be an integer. Consider the sparsity constrained problem $\min\{f(x):\|x\|_0\le s\}$.
--
--   If $x^*\in C_s$ is a coordinate-wise minimum of (P) (Definition 2.4), then $x^*$ is a basic feasible vector (Definition 2.1):
--   $$\|x^*\|_0<s\ \Rightarrow\ \nabla f(x^*)=0,\qquad \|x^*\|_0=s\ \Rightarrow\ \nabla_i f(x^*)=0\ \text{ for all } i\in I_1(x^*).$$
--
--   The lemma says that the coordinate-wise optimality condition is at least as strong as basic feasibility. In the proof of Theorem 2.4 it supplies the vanishing of the gradient on the support, (2.14).
--
--   **Formalization Note** Assumption 1 (a lower bound $\gamma\le f$) is the paper's standing assumption and is kept as a hypothesis, although the statement does not need it. The hypothesis $x^*\in C_s$ repeats the feasibility built into the definition of a CW-minimum, as the page does.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), p. 10, Lemma 2.5

import Mathlib
import Definitions.Def_SparseNLO_CWOpt_Setting

namespace SparseNLO.CWOpt

/-- Lemma 2.5 (p. 10): every CW-minimum of (P) is a BF vector. -/
theorem lemma_2_5 {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x) (hs : 0 < s) (hsn : s < n)
    (xstar : EuclideanSpace ℝ (Fin n)) (hx : xstar ∈ Cs n s) (hcw : IsCWMin f s xstar) :
    IsBF f s xstar := by sorry

end SparseNLO.CWOpt
