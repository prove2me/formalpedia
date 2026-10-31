-- Prove2me | Theorems.Thm_ShapleyNV_thm1_proof_lambda_zero
-- name    : ShapleyNV.thm1_proof_lambda_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:54:05.906516+00:00
-- url     : https://prove2.me/theorems/742e3f21-05bd-4e6c-ac19-5f5c49c78aa2
-- title:
--   Proof of Theorem 1, p.ec4 — for $\lambda=0$: $\Psi(f(x),z)\le\max_{x'\in\widehat{\mathcal X}}\Psi(\hat f(x'),z)$
-- statement:
--   Let $b > 0$, $0 \le h \le b$, and let $\hat f \ge 0$ be an in-sample policy with Shapley extension $f$. Since the range of $f$ is contained in $[\min \hat f, \max \hat f]$ and $\Psi(\cdot, z)$ is convex, the supremum of $\Psi(f(\cdot), z)$ is attained at the extreme points: for every $x \in \mathcal X$ and every demand $z$,
--
--   $$
--   \Psi(f(x), z) \le \max_{x' \in \widehat{\mathcal X}} \Psi(\hat f(x'), z).
--   $$
--
--   Taking suprema over $x$ and $z$ and the expectation over $\widehat{\mathbb P}$ gives the paper's display
--   $\mathbb E_{\widehat{\mathbb P}}\big[\sup_{z}\sup_{x \in \mathcal X} \Psi(f(x), z)\big] \le \mathbb E_{\widehat{\mathbb P}}\big[\sup_{z} \max_{x \in \widehat{\mathcal X}} \Psi(\hat f(x), z)\big]$.
--
--   Differences from the source:
--   - generalization: E_P̂[sup_z sup_x Ψ(f(x), z)] ≤ E_P̂[sup_z max_{x∈𝒳̂} Ψ(f̂(x), z)] → Ψ(f(x), z) ≤ max_k Ψ(y_k, z) for every x and every real z; reason: the pointwise inequality is what the sentence asserts and implies the display by taking suprema and expectations
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), proof of Theorem 1, case λ = 0, p.ec4 (PDF 25)

import Mathlib
import Definitions.Def_ShapleyNV_nvCost
import Definitions.Def_ShapleyNV_shapley

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Proof of Theorem 1, the case `λ = 0`**, p.ec4: the range of the Shapley extension `f` is in
`[min f̂, max f̂]` and `Ψ(·, z)` is convex, so the supremum of `Ψ(f(·), z)` is attained at the
in-sample points: `Ψ(f(x), z) ≤ max_{x'∈𝒳̂} Ψ(f̂(x'), z)`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), proof of Theorem 1, the case `λ = 0`, p.ec4 (PDF 25).

**Formalization Note.** Stated pointwise for every `x` and every real `z`; taking suprema over
`z`, `x` and the expectation over `P̂` gives the printed display. -/
theorem thm1_proof_lambda_zero {X : Type*} [MetricSpace X] (D : Data X) (h b : ℝ) (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b)
    (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) (z : ℝ) (x : X) :
    nvCost h b (shapley D y x) z ≤ Finset.univ.sup' D.univ_nonempty (fun k => nvCost h b (y k) z) := by sorry

end ShapleyNV
