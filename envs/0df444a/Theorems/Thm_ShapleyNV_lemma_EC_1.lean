-- Prove2me | Theorems.Thm_ShapleyNV_lemma_EC_1
-- name    : ShapleyNV.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:55:02.99105+00:00
-- url     : https://prove2.me/theorems/5180870a-7b1d-447c-895e-25e60216b760
-- title:
--   Lemma EC.1, p.ec1 — strong duality $v_P^f = v_D^f$ for each policy (corrected: $\rho > 0$)
-- statement:
--   Let $\widehat{\mathbb P}$ be the empirical distribution of the data, let $b > 0$ and $0 \le h \le b$, and let $\rho > 0$. For each measurable policy $f : \mathcal X \to \mathbb R_+$, the inner primal problem
--
--   $$
--   v_P^f := \sup_{\mathbb P \in \mathcal P_1(\mathcal X \times \mathcal Z)} \Big\{ \mathbb E_{(X,Z)\sim\mathbb P}\big[\Psi(f(X), Z)\big] : \mathcal W(\mathbb P, \widehat{\mathbb P}) \le \rho \Big\}
--   $$
--
--   is equal to the inner dual problem
--
--   $$
--   v_D^f := \inf_{\lambda \ge 0} \Big\{ \lambda\rho + \mathbb E_{(\hat X,\hat Z)\sim\widehat{\mathbb P}}\Big[ \sup_{(x,z) \in \mathcal X \times \mathcal Z} \big\{ \Psi(f(x), z) - \lambda(\|x - \hat X\| + |z - \hat Z|) \big\} \Big] \Big\}.
--   $$
--
--   Both values may be $+\infty$.
--
--   This strong duality turns the infinite-dimensional worst case over distributions into a one-dimensional minimization over $\lambda$.
--
--   **Formalization Note** The paper allows $\rho \ge 0$. At $\rho = 0$ the lemma fails: with $\mathcal X = \mathbb R$, $K = 1$, $\hat x_1 = 0$, one observation $\hat z_{11} = 0$, $h = b = 1$ and $f(x) = x^2$, the ball is $\{\widehat{\mathbb P}\}$ so $v_P^f = 0$, while for every $\lambda$ the inner supremum is at least $\sup_x (x^2 - \lambda|x|) = +\infty$, so $v_D^f = +\infty$. The statement therefore assumes $\rho > 0$. Theorem 1 does not depend on this: its proof uses only weak duality, which holds at $\rho = 0$.
--
--   Differences from the source:
--   - correction: for each f ∈ ℱ and ρ ≥ 0 → 0 < ρ; reason: false at ρ = 0: 𝒳 = ℝ, K = 1, x̂ = 0, ẑ = 0, h = b = 1, f(x) = x² gives v_P^f = 0 and v_D^f = +∞
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) with its Borel σ-algebra → any second-countable metric space X with its Borel σ-algebra; reason: the paper's 𝒳 is such a space; nothing beyond metric and measurability properties is used
--   - encoding: real or infinite optimal values, 𝒵 = ℝ₊ → values in ℝ≥0∞, demands in ℝ≥0, policies as real functions with f ≥ 0; reason: Ψ ≥ 0 and the values may be +∞ (p.ec1); same instances
--   - encoding: W(P, P̂) with cost ‖x̃ − x‖ + |z̃ − z| → transportCost with fullCost = dist x x' + dist z z' (the sum, not Lean's max metric); reason: same cost
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma EC.1, p.ec1 (PDF 22); standing assumptions b > 0, 0 ≤ h ≤ b (p.6) and ρ ≥ 0 (p.5)

import Mathlib
import Definitions.Def_ShapleyNV_fullWorst
import Definitions.Def_ShapleyNV_fullDual

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Lemma EC.1 (corrected: ρ > 0)**, p.ec1: for each `f ∈ ℱ`, the inner primal problem
`v_P^f := sup_{P∈𝒫₁(𝒳×𝒵)} { E_P[Ψ_f(X, Z)] : W(P, P̂) ≤ ρ }` equals the inner dual problem
`v_D^f := inf_{λ≥0} ( λρ + E_{(X̂,Ẑ)∼P̂}[ sup_{(x,z)∈𝒳×𝒵} { Ψ_f(x, z) − λ(‖x − X̂‖ + |z − Ẑ|) } ] )`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma EC.1, p.ec1 (PDF 22).

**Formalization Note.** Both values are in `ℝ≥0∞` and may be `+∞` (as the paper notes). The
hypothesis `0 < ρ` corrects the printed statement, which allows `ρ = 0` (p.5): with `𝒳 = ℝ`,
`K = 1`, `x̂_1 = 0`, `ẑ_11 = 0`, `h = b = 1`, `ρ = 0` and `f(x) = x²`, the primal value is `0`
and the dual value is `+∞`. Standing assumption `b > 0`, `0 ≤ h ≤ b` (p.6). -/
theorem lemma_EC_1 {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (D : Data X) (h b ρ : ℝ) (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b)
    (hρ : 0 < ρ) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    fullWorst D h b ρ f = fullDual D h b ρ f := by sorry

end ShapleyNV
