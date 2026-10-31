-- Prove2me | Theorems.Thm_ShapleyNV_thm1_proof_dual_eq
-- name    : ShapleyNV.thm1_proof_dual_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:55:57.746854+00:00
-- url     : https://prove2.me/theorems/047be212-31d1-4652-a6dc-a0ced480137e
-- title:
--   Proof of Theorem 1, p.ec4 — $v_D = v_{\widehat D}$, and the Shapley extension of a minimizer of $v_{\widehat D}$ minimizes $v_D$
-- statement:
--   Let $b > 0$, $0 \le h \le b$ and $\rho \ge 0$. Then:
--
--   1. for every in-sample policy $\hat f \ge 0$ with Shapley extension $f$, the inner dual value of $f$ is at most the inner in-sample dual value of $\hat f$:
--   $$
--   \inf_{\lambda\ge0}\Big\{\lambda\rho + \mathbb E_{\widehat{\mathbb P}}\Big[\sup_{z\in\mathcal Z,\,x\in\mathcal X}\{\Psi(f(x),z) - \lambda\|x-\hat X\| - \lambda|z-\hat Z|\}\Big]\Big\} \le \inf_{\lambda\ge0}\Big\{\lambda\rho + \mathbb E_{\widehat{\mathbb P}}\Big[\sup_{z\in\mathcal Z}\max_{x\in\widehat{\mathcal X}}\{\Psi(\hat f(x),z) - \lambda\|x-\hat X\| - \lambda|z-\hat Z|\}\Big]\Big\};
--   $$
--   2. the dual problems have equal values, $v_D = v_{\widehat D}$;
--   3. if $\hat f^*$ is a minimizer of $v_{\widehat D}$, then its Shapley extension is a minimizer of $v_D$: it is a measurable policy with values in $\mathcal Z = \mathbb R_+$, and its inner dual value equals $v_D$.
--
--   Differences from the source:
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) with its Borel σ-algebra → any second-countable metric space X with its Borel σ-algebra; reason: the paper's 𝒳 is such a space; nothing beyond metric and measurability properties is used
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
--   - encoding: real or infinite optimal values, 𝒵 = ℝ₊ → values in ℝ≥0∞, demands in ℝ≥0, policies as real functions with f ≥ 0; reason: Ψ ≥ 0 and the values may be +∞ (p.ec1); same instances
--   - encoding: f̂* a minimizer of v_D̂ (jointly with λ) → y ≥ 0 whose inner in-sample dual value equals v_D̂; reason: the joint minimum over (f̂, λ) is the minimum over f̂ of the inner infimum over λ
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), proof of Theorem 1, p.ec4 (PDF 25)

import Mathlib
import Definitions.Def_ShapleyNV_fullDual
import Definitions.Def_ShapleyNV_inDual
import Definitions.Def_ShapleyNV_vD
import Definitions.Def_ShapleyNV_vDhat
import Definitions.Def_ShapleyNV_shapley

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Proof of Theorem 1: `v_D = v_D̂`**, p.ec4. For every in-sample policy `f̂`, the inner dual value
of its Shapley extension is at most the inner in-sample dual value of `f̂`; `v_D = v_D̂`; and the
Shapley extension of a minimizer of `v_D̂` is a minimizer of `v_D` (a measurable policy with values in
`𝒵 = ℝ₊` attaining `v_D`).
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), proof of Theorem 1, p.ec4 (PDF 25). -/
theorem thm1_proof_dual_eq {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (D : Data X) (h b ρ : ℝ) (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b) (hρ : 0 ≤ ρ) :
    (∀ y : Fin D.K → ℝ, (∀ k, 0 ≤ y k) → fullDual D h b ρ (shapley D y) ≤ inDual D h b ρ y) ∧
    vD D h b ρ = vDhat D h b ρ ∧
    (∀ y : Fin D.K → ℝ, (∀ k, 0 ≤ y k) → inDual D h b ρ y = vDhat D h b ρ →
      Measurable (shapley D y) ∧ (∀ x, 0 ≤ shapley D y x) ∧
        fullDual D h b ρ (shapley D y) = vD D h b ρ) := by sorry

end ShapleyNV
