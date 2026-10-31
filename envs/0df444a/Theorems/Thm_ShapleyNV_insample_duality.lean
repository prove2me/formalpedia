-- Prove2me | Theorems.Thm_ShapleyNV_insample_duality
-- name    : ShapleyNV.insample_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:54:31.64587+00:00
-- url     : https://prove2.me/theorems/5d5c31ca-c9f2-46d4-9ef7-2934d7169867
-- title:
--   §3.1, p.7 — in-sample strong duality: $(\widehat{\mathrm P})$ equals $(\widehat{\mathrm D})$ for each in-sample policy
-- statement:
--   Let $b > 0$, $0 \le h \le b$ and $\rho \ge 0$. For every in-sample policy $\hat f : \widehat{\mathcal X} \to \mathbb R_+$,
--
--   $$
--   \sup_{\mathbb P \in \mathcal P_1(\widehat{\mathcal X} \times \mathcal Z)} \Big\{ \mathbb E_{\mathbb P}\big[\Psi(\hat f(X), Z)\big] : \mathcal W(\mathbb P, \widehat{\mathbb P}) \le \rho \Big\}
--   = \inf_{\lambda \ge 0} \Big\{ \lambda\rho + \mathbb E_{(\hat X,\hat Z)\sim\widehat{\mathbb P}}\Big[ \sup_{z \in \mathcal Z} \max_{x \in \widehat{\mathcal X}} \big\{ \Psi(\hat f(x), z) - \lambda\|x - \hat X\| - \lambda|z - \hat Z| \big\} \Big] \Big\}.
--   $$
--
--   Taking the infimum over $\hat f$ gives $v_{\widehat P} = v_{\widehat D}$: the in-sample dual problem $(\widehat{\mathrm D})$ is an equivalent reformulation of $(\widehat{\mathrm P})$.
--
--   **Formalization Note** Unlike Lemma EC.1 on the full feature space, this holds at $\rho = 0$ as well: the in-sample feature set is finite and $\Psi(y, \cdot)$ is Lipschitz.
--
--   Differences from the source:
--   - generalization: v_P̂ = v_D̂ (problem level) → equality of the inner values for every in-sample policy y; reason: taking the infimum over y gives the problem-level equality
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
--   - encoding: real or infinite optimal values, 𝒵 = ℝ₊ → values in ℝ≥0∞, demands in ℝ≥0, policies as real functions with f ≥ 0; reason: Ψ ≥ 0 and the values may be +∞ (p.ec1); same instances
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), §3.1, p.7 (strong duality applied to the inner maximization of (P̂), (D̂)); p.6 ((D̂) is an equivalent reformulation of (P̂))

import Mathlib
import Definitions.Def_ShapleyNV_inWorst
import Definitions.Def_ShapleyNV_inDual

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **In-sample strong duality** (P̂) = (D̂), pp.6–7: for every in-sample policy `f̂`, the inner
supremum of (P̂) equals the inner dual of (D̂),
`inf_{λ≥0} ( λρ + E_P̂[ sup_{z∈𝒵} max_{x∈𝒳̂} { Ψ(f̂(x), z) − λ‖x − X̂‖ − λ|z − Ẑ| } ] )`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), §3.1, p.7 ("applying strong duality … on the inner maximization of (P) and (P̂)
respectively yields their strong dual problems", (D̂)); p.6 ("(D̂) … is an equivalent
reformulation of the in-sample robust primal problem (P̂)").

**Formalization Note.** Stated for each policy (per `f̂`), which gives `v_P̂ = v_D̂` by taking the
infimum. It holds for every `ρ ≥ 0`, including `ρ = 0`. -/
theorem insample_duality {X : Type*} [MetricSpace X] (D : Data X) (h b ρ : ℝ) (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b)
    (hρ : 0 ≤ ρ) (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) :
    inWorst D h b ρ y = inDual D h b ρ y := by sorry

end ShapleyNV
