-- Prove2me | Theorems.Thm_RobustRegLasso_WorstCaseExp_appendix_d_box_decomposition
-- name    : RobustRegLasso.WorstCaseExp.appendix_d_box_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:19:00.609574+00:00
-- url     : https://prove2.me/theorems/86810e25-6b61-4796-9953-0a67b3cedcfa
-- title:
--   Appendix D, second and third displays — the worst-case residual as a supremum over the boxes $\mathcal Z_i$, sample by sample
-- statement:
--   Let $n\ge1$ and $m$ be integers, $b\in\mathbb R^n$, $A=(a_{ij})\in\mathbb R^{n\times m}$ with rows $r_i^\top$, $c\ge0$ and $x\in\mathbb R^m$. For an admissible pair $(\sigma,\Delta)$ (that is, $\|\sigma\|_2\le\sqrt n\,c$ and every column of $\Delta=(\delta_{ij})$ has Euclidean norm at most $\sqrt n\,c$) let
--   $$\mathcal Z_i(\sigma,\Delta)=[b_i-\sigma_i,b_i+\sigma_i]\times\prod_{j=1}^m[a_{ij}-\delta_{ij},a_{ij}+\delta_{ij}]\subseteq\mathbb R^{m+1}\qquad(i=1,\dots,n).$$
--   Then the following three suprema over admissible $(\sigma,\Delta)$ coincide:
--   $$\sup_{(\sigma,\Delta)}\big\|b+\sigma-(A+\Delta)x\big\|_2
--   =\sup_{(\sigma,\Delta)}\Big\{\sup_{(\hat b_i,\hat r_i)\in\mathcal Z_i(\sigma,\Delta)}\sqrt{\sum_{i=1}^n(\hat b_i-\hat r_i^\top x)^2}\Big\}
--   =\sup_{(\sigma,\Delta)}\sqrt{\sum_{i=1}^n\ \sup_{(\hat b_i,\hat r_i)\in\mathcal Z_i(\sigma,\Delta)}(\hat b_i-\hat r_i^\top x)^2}.$$
--   In the middle term one point $(\hat b_i,\hat r_i)$ is chosen in each box.
--
--   The identity separates the worst case over a perturbation of the whole data set into a sum of per-sample worst cases over boxes, which is the form to which Proposition 1 applies.
--
--   **Formalization Note** "The suprema coincide" is stated without any real `sSup`: for every real $L$, $L$ is the least upper bound of the first set iff it is the least upper bound of the second, iff it is the least upper bound of the third. A box with some $\sigma_i<0$ or $\delta_{ij}<0$ is empty; such $(\sigma,\Delta)$ contribute no value to the second and third sets (the page leaves this case silent). The inner supremum over a nonempty box is attained, since the box is compact and the loss is continuous; in the third set it is encoded as the greatest value $s_i$ of the loss on $\mathcal Z_i$ (`IsGreatest`), which exists exactly when the box is nonempty. Points of $\mathbb R^{m+1}$ have the response first. The hypotheses $n\ge1$, $c\ge0$ are the paper's setting.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 22, Appendix D, proof of Corollary 3, second and third displays

import Mathlib
import Definitions.Def_RobustRegLasso_WorstCaseExp_Basic

namespace RobustRegLasso.WorstCaseExp

/-- Appendix D, proof of Corollary 3, second and third displays (arXiv:0811.1790v1, p. 22).
Over the admissible `(σ, Δ)`, the three quantities
1. `‖b + σ − (A + Δ)x‖₂`,
2. `√(∑ᵢ (b̂ᵢ − r̂ᵢᵀx)²)` for points `(b̂ᵢ, r̂ᵢ) ∈ 𝒵ᵢ(σ, Δ)`, one per sample,
3. `√(∑ᵢ sᵢ)` with `sᵢ = max_{(b̂ᵢ, r̂ᵢ) ∈ 𝒵ᵢ(σ, Δ)} (b̂ᵢ − r̂ᵢᵀx)²`,
have the same supremum: a real number is the least upper bound of the first set iff it is the
least upper bound of the second, iff it is the least upper bound of the third. -/
theorem appendix_d_box_decomposition {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (x : Fin m → ℝ) (L : ℝ) :
    (IsLUB {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ v = l2norm (b + σ - Matrix.mulVec (A + Δ) x)} L ↔
      IsLUB {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ ∃ p : Fin n → Fin (m + 1) → ℝ,
          (∀ i, p i ∈ box A b σ Δ i) ∧ v = Real.sqrt (∑ i, sqLoss x (p i))} L) ∧
    (IsLUB {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ ∃ p : Fin n → Fin (m + 1) → ℝ,
          (∀ i, p i ∈ box A b σ Δ i) ∧ v = Real.sqrt (∑ i, sqLoss x (p i))} L ↔
      IsLUB {v : ℝ | ∃ (σ : Fin n → ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ),
        Admissible c σ Δ ∧ ∃ s : Fin n → ℝ,
          (∀ i, IsGreatest (sqLoss x '' box A b σ Δ i) (s i)) ∧
            v = Real.sqrt (∑ i, s i)} L) := by sorry

end RobustRegLasso.WorstCaseExp
