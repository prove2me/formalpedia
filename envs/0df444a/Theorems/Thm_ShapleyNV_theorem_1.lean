-- Prove2me | Theorems.Thm_ShapleyNV_theorem_1
-- name    : ShapleyNV.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:55:50.081235+00:00
-- url     : https://prove2.me/theorems/dc51c0c1-14de-4272-b02b-facb7e608356
-- title:
--   Theorem 1, p.6 — the Shapley extension of an optimal in-sample robust policy is optimal for (P)
-- statement:
--   Consider the Wasserstein robust feature-based newsvendor problem (P): data with $K \ge 1$ distinct observed features $\hat x_k \in \mathcal X$, each with $n_k \ge 1$ demand observations $\hat z_{ki} \ge 0$, empirical distribution $\widehat{\mathbb P}$, cost $\Psi(y,z) = h(y-z)^+ + b(z-y)^+$ with $b > 0$ and $0 \le h \le b$, and radius $\rho \ge 0$. Then (P) is solved in two steps:
--
--   1. **(In-sample robust policy.)** The in-sample problem
--   $$
--   v_{\widehat P} := \min_{\hat f : \widehat{\mathcal X} \to \mathcal Z}\ \sup_{\mathbb P \in \mathcal P_1(\widehat{\mathcal X} \times \mathcal Z)} \Big\{ \mathbb E_{\mathbb P}\big[\Psi(\hat f(X), Z)\big] : \mathcal W(\mathbb P, \widehat{\mathbb P}) \le \rho \Big\}
--   $$
--   attains its minimum, and its value equals that of (P): $v_P = v_{\widehat P}$.
--   2. **(Shapley extension.)** For **every** optimal in-sample policy $\hat f^*$, the matrix
--   $$
--   A_{jk}(x) := \frac{\|x - \hat x_k\|}{\|x - \hat x_j\| + \|x - \hat x_k\|}\hat f^*(\hat x_j) + \frac{\|x - \hat x_j\|}{\|x - \hat x_j\| + \|x - \hat x_k\|}\hat f^*(\hat x_k) \quad (j \ne k), \qquad A_{kk}(x) := \hat f^*(\hat x_k),
--   $$
--   has a saddle point at every $x$, so that
--   $$
--   f^*(x) := \min_{j\in[K]} \max_{k\in[K]} A_{jk}(x) = \max_{k\in[K]} \min_{j\in[K]} A_{jk}(x),
--   $$
--   and $f^*$ is an optimal policy for (P): it is measurable, takes values in $\mathcal Z = \mathbb R_+$, and its worst-case expected cost equals $v_P$.
--
--   The infinite-dimensional problem over all measurable policies is thereby reduced to a finite-dimensional problem over $\mathbb R_+^K$ followed by an explicit extension formula.
--
--   Differences from the source:
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) with its Borel σ-algebra → any second-countable metric space X with its Borel σ-algebra; reason: the paper's 𝒳 is such a space; nothing beyond metric and measurability properties is used
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
--   - encoding: real or infinite optimal values, 𝒵 = ℝ₊ → values in ℝ≥0∞, demands in ℝ≥0, policies as real functions with f ≥ 0; reason: Ψ ≥ 0 and the values may be +∞ (p.ec1); same instances
--   - encoding: A_kk(x) from the single formula of Theorem 1 (0/0 at x = x̂_k) → A_kk(x) := f̂(x̂_k); reason: this is Lemma 1 (S), p.7; for j ≠ k the formulas coincide
--   - reading: 'Problem (P) can be solved in two steps', 'min' in (P̂), 'the optimal solution', 'an optimal policy f* for problem (P)' → v_P = v_P̂; (P̂) has a minimizer; for every minimizer the saddle point exists and f* is measurable, nonnegative and attains v_P; reason: the stronger reading of each phrase; v_P = v_P̂ is the conclusion of the proof on p.ec4
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Theorem 1, p.6; standing assumptions b > 0, 0 ≤ h ≤ b (p.6), ρ ≥ 0 (p.5), distinct x̂_k (p.5)

import Mathlib
import Definitions.Def_ShapleyNV_vP
import Definitions.Def_ShapleyNV_vPhat
import Definitions.Def_ShapleyNV_shapley
import Definitions.Def_ShapleyNV_shapleyLower

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Theorem 1**, p.6: problem (P) can be solved in two steps.
(I) Solve the in-sample primal problem (P̂), which has an optimal solution `f̂*`.
(II) The Shapley extension `f*(x) := min_j max_k A_jk(x) = max_k min_j A_jk(x)` of `f̂*` is an optimal
policy for (P).
Formally: `v_P = v_P̂`; (P̂) attains its minimum; and for **every** minimizer `f̂*` of (P̂), the
matrix `A(x)` has a saddle point at every `x`, and `f*` is a measurable policy with values in `𝒵`
whose worst-case expected cost equals `v_P`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Theorem 1, p.6.

**Formalization Note.** The feature space is a second-countable metric space with its Borel
σ-algebra (the paper's `𝒳 ⊂ (ℝ^d, ‖·‖)` is one). `𝒳̂` is `Fin K`, in-sample policies are vectors
`y ≥ 0`, values are in `ℝ≥0∞`, and `A_kk := f̂(x̂_k)` as in Lemma 1 (S). Standing assumptions
`b > 0`, `0 ≤ h ≤ b`, `ρ ≥ 0` (pp.5–6). -/
theorem theorem_1 {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (D : Data X) (h b ρ : ℝ) (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b) (hρ : 0 ≤ ρ) :
    vP D h b ρ = vPhat D h b ρ ∧
    (∃ y : Fin D.K → ℝ, (∀ k, 0 ≤ y k) ∧ inWorst D h b ρ y = vPhat D h b ρ) ∧
    ∀ y : Fin D.K → ℝ, (∀ k, 0 ≤ y k) → inWorst D h b ρ y = vPhat D h b ρ →
      (∀ x, shapley D y x = shapleyLower D y x) ∧
      Measurable (shapley D y) ∧ (∀ x, 0 ≤ shapley D y x) ∧
      fullWorst D h b ρ (shapley D y) = vP D h b ρ := by sorry

end ShapleyNV
