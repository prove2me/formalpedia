-- Prove2me | Theorems.Thm_ShapleyNV_eq_EC_2
-- name    : ShapleyNV.eq_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:50.43747+00:00
-- url     : https://prove2.me/theorems/c5a12ae4-4d84-491e-b910-9af8c23fcad7
-- title:
--   (EC.2), p.ec6 — in $(\widehat{\mathrm D})$ one may take $\lambda\ge b\vee h$ and drop the supremum over $z$
-- statement:
--   Let $b > 0$, $0 \le h \le b$ and $\rho \ge 0$. For every in-sample policy $\hat f \ge 0$,
--
--   $$
--   \inf_{\lambda\ge0}\Big\{\lambda\rho + \mathbb E_{\widehat{\mathbb P}}\Big[\sup_{z\in\mathcal Z}\max_{x\in\widehat{\mathcal X}}\{\Psi(\hat f(x),z) - \lambda\|x-\hat X\| - \lambda|z-\hat Z|\}\Big]\Big\}
--   = \inf_{\lambda \ge b \vee h}\Big\{\lambda\rho + \mathbb E_{\widehat{\mathbb P}}\Big[\max_{x \in \widehat{\mathcal X}}\big\{\Psi(\hat f(x), \hat Z) - \lambda\|x - \hat X\|\big\}\Big]\Big\}.
--   $$
--
--   Taking the infimum over $\hat f$ gives (EC.2):
--   $$
--   v_{\widehat D} = \min_{\hat f \in \widehat{\mathcal F},\, \lambda \ge b \vee h} \Big\{\lambda\rho + \mathbb E_{\widehat{\mathbb P}}\Big[\max_{x \in \widehat{\mathcal X}}\big\{\Psi_{\hat f}(x, \hat Z) - \lambda\|x - \hat X\|\big\}\Big]\Big\}.
--   $$
--
--   For $\lambda < b \vee h$ the inner supremum over $z$ is infinite; for $\lambda \ge b \vee h$ it is attained at $z = \hat Z$.
--
--   Differences from the source:
--   - generalization: (EC.2), an identity of optimal values → the identity for every in-sample policy y; reason: taking the infimum over y gives (EC.2)
--   - reading: 'min' in (EC.2) → infimum (value identity); attainment is not claimed here; reason: attainment is proved separately at the end of the proof of Proposition 1 and is a clause of ShapleyNV.theorem_1
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
--   - encoding: real or infinite optimal values, 𝒵 = ℝ₊ → values in ℝ≥0∞, demands in ℝ≥0, policies as real functions with f ≥ 0; reason: Ψ ≥ 0 and the values may be +∞ (p.ec1); same instances
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), proof of Proposition 1, eq. (EC.2), p.ec6 (PDF 27), justified on p.ec7 (PDF 28)

import Mathlib
import Definitions.Def_ShapleyNV_nvCost
import Definitions.Def_ShapleyNV_PhatIn
import Definitions.Def_ShapleyNV_inDual

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **(EC.2)**, proof of Proposition 1, p.ec6: in (D̂) the multiplier can be restricted to
`λ ≥ b ∨ h` and the supremum over `z` drops out:
`v_D̂ = min_{f̂ ∈ ℱ̂, λ ≥ b∨h} λρ + E_P̂[ max_{x∈𝒳̂} { Ψ_f̂(x, Ẑ) − λ‖x − X̂‖ } ]`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), proof of Proposition 1, eq. (EC.2), p.ec6 (PDF 27), with its justification on p.ec7.

**Formalization Note.** Stated for each in-sample policy `f̂` (vector `y`): the inner in-sample dual
value equals the infimum over `λ ≥ b ∨ h` of the right-hand objective. Taking the infimum over `y`
gives (EC.2). The maximum inside is at least `Ψ(f̂(X̂), Ẑ) ≥ 0`, so `ENNReal.ofReal` is harmless. -/
theorem eq_EC_2 {X : Type*} [MetricSpace X] (D : Data X) (h b ρ : ℝ) (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b) (hρ : 0 ≤ ρ)
    (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) :
    inDual D h b ρ y =
      ⨅ lam : ℝ, ⨅ (_ : max b h ≤ lam), ENNReal.ofReal (lam * ρ) +
        ∫⁻ ξh, ENNReal.ofReal (Finset.univ.sup' D.univ_nonempty
          (fun k => nvCost h b (y k) ξh.2 - lam * dist (D.xhat k) (D.xhat ξh.1))) ∂(PhatIn D) := by sorry

end ShapleyNV
