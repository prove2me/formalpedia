-- Prove2me | Theorems.Thm_ShapleyNV_thm1_proof_lambda_pos
-- name    : ShapleyNV.thm1_proof_lambda_pos
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:53:57.032054+00:00
-- url     : https://prove2.me/theorems/8e5fd0bc-14a3-4f02-8718-ffbda88924f9
-- title:
--   Proof of Theorem 1, p.ec4 — for $\lambda>0$ the Shapley extension does not increase the dual's inner supremum
-- statement:
--   Let $b > 0$, $0 \le h \le b$, let $\hat f \ge 0$ be an in-sample policy with Shapley extension $f$, and let $\lambda > 0$. Then for every observed feature $\hat X \in \widehat{\mathcal X}$ and every demand $z$,
--
--   $$
--   \sup_{x \in \mathcal X} \big\{ \Psi(f(x), z) - \lambda\|x - \hat X\| \big\} \le \max_{x \in \widehat{\mathcal X}} \big\{ \Psi(\hat f(x), z) - \lambda\|x - \hat X\| \big\}.
--   $$
--
--   It follows from (5) with the convex function $\Phi = \Psi(\cdot, z)/\lambda$.
--
--   Differences from the source:
--   - generalization: z ∈ 𝒵 = ℝ₊ → every real z; reason: Ψ(·, z) is convex for every real z; the paper's range is a special case
--   - generalization: 𝒳 ⊂ (ℝ^d, ‖·‖) → any metric space X, ‖x − x'‖ read as dist x x'; reason: the proof uses only the triangle inequality, symmetry and positivity of distances; the paper's 𝒳 with dist = ‖·‖ is an instance
--   - encoding: in-sample policy f̂ : 𝒳̂ → 𝒵 → vector y : Fin K → ℝ with y ≥ 0, y k = f̂(x̂_k); reason: Remark 1 identifies ℱ̂ with a subset of ℝ₊^K; 𝒳̂ is indexed by Fin K through the injective x̂
--   - encoding: sup over x ∈ 𝒳, X̂ ∈ 𝒳̂ → the inequality for every x, with X̂ = x̂_k'; reason: the right side does not depend on x
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), proof of Theorem 1, first display, p.ec4 (PDF 25)

import Mathlib
import Definitions.Def_ShapleyNV_nvCost
import Definitions.Def_ShapleyNV_shapley

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Proof of Theorem 1, the case `λ > 0`**, p.ec4: the Shapley extension `f` of `f̂` satisfies
`sup_{x∈𝒳} { Ψ(f(x), z) − λ‖x − X̂‖ } ≤ max_{x∈𝒳̂} { Ψ(f̂(x), z) − λ‖x − X̂‖ }` for all `X̂ ∈ 𝒳̂`, `z ∈ 𝒵`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), proof of Theorem 1, first display, p.ec4 (PDF 25).

**Formalization Note.** `X̂ = x̂_k'`; the supremum over `x` is the inequality for every `x`; the
demand `z` ranges over all of `ℝ` (the paper: `z ∈ 𝒵 = ℝ₊`). -/
theorem thm1_proof_lambda_pos {X : Type*} [MetricSpace X] (D : Data X) (h b : ℝ) (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b)
    (y : Fin D.K → ℝ) (hy : ∀ k, 0 ≤ y k) (lam : ℝ) (hlam : 0 < lam) (k' : Fin D.K) (z : ℝ) (x : X) :
    nvCost h b (shapley D y x) z - lam * dist x (D.xhat k') ≤
      Finset.univ.sup' D.univ_nonempty
        (fun k => nvCost h b (y k) z - lam * dist (D.xhat k) (D.xhat k')) := by sorry

end ShapleyNV
