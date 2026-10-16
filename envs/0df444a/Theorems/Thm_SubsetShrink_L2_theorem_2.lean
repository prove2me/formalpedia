-- Prove2me | Theorems.Thm_SubsetShrink_L2_theorem_2
-- name    : SubsetShrink.L2.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:25.747861+00:00
-- url     : https://prove2.me/theorems/03ee83fe-912f-422b-a644-7a5d7e6bdbc5
-- title:
--   Theorem 2, p. 14 — slow-rate (on E_2k and F) and fast-rate (on G_2k) oracle inequalities for ℓ2-regularized best subsets
-- statement:
--   Consider the model $y=f^*+\epsilon$ with a design $X\in\mathbb R^{n\times p}$ whose columns have unit Euclidean norm, a noise level $\sigma>0$, and a model size $1\le k\le p$. Let $\hat\beta_2$ be any $\ell_2$-regularized best-subsets solution of (16), i.e. any minimizer of $\|y-X\beta\|^2+\lambda\|\beta\|$ subject to $\|\beta\|_0\le k$.
--
--   **(A) Slow rate.** If $\lambda\ge[8+2\sqrt2]\,\sigma\sqrt{2k\log(ep/k)}$, then on the event $\mathcal E_{2k}$,
--   $$\|f^*-X\hat\beta_2\|^2\le\inf_{\beta\in B_0(k)}\big[\|f^*-X\beta\|^2+2\lambda\|\beta\|\big];$$
--   and on the event $\mathcal F$, for any $\delta_0\in(0,1]$,
--   $$\|f^*-X\hat\beta_2\|^2\lesssim\inf_{\beta\in B_0(k)}\big[\|f^*-X\beta\|^2+\lambda\|\beta\|\big]+\sigma^2\log(1/\delta_0).$$
--
--   **(B) Fast rate.** For every $\lambda\ge0$, on the event $\mathcal G_{2k}$, for any $\delta_0\in(0,1]$,
--   $$\|f^*-X\hat\beta_2\|^2\lesssim\inf_{\beta\in B_0(k)}\|f^*-X\beta\|^2+\sigma^2k\log(ep/k)+\gamma_{2k}^{-2}\lambda^2+\sigma^2\log(1/\delta_0).$$
--
--   Here $\lesssim$ means "up to a positive universal multiplicative constant". The slow rates are linear in $\lambda$ and are the relevant ones when the signal-to-noise ratio is low; the fast rate recovers the minimax rate $\sigma^2k\log(ep/k)$ up to the shrinkage term $\gamma_{2k}^{-2}\lambda^2$.
--
--   **Formalization Note**
--   1. The statement is a conjunction of three parts. Part (A1) has no constant. Parts (A2) and (B) each assert the existence of their own constant $C>0$, chosen before $n,p,k,X,f^*,\epsilon,\sigma,\delta_0,\lambda,\hat\beta_2$ and $\beta$.
--   2. "$\le C(\inf_{\beta\in B_0(k)} g(\beta)+h)$" is stated as "$\le C(g(\beta)+h)$ for every $\beta\in B_0(k)$", which is equivalent for fixed $C$ and avoids real infima.
--   3. "On the event" means the noise vector $\epsilon$ satisfies the event's defining inequality; the statement is deterministic. $\delta_0$ is the events' parameter and is universally quantified.
--   4. In (B) the hypothesis $\gamma_{2k}>0$ or $\lambda=0$ is added: when $\gamma_{2k}=0<\lambda$ the paper's term $\gamma_{2k}^{-2}\lambda^2$ is $+\infty$ and the bound is vacuous, while Lean's $0^{-1}=0$ would make it a false claim; when $\lambda=0$ the term is $0$ by the paper's convention $0\cdot\infty=0/0=0$, and also in Lean.
--   5. $\mathcal G_{2k}$ is the event as printed on p. 13.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 14, Theorem 2; proof B.2, pp. 39–40

import Mathlib
import Definitions.Def_SubsetShrink_L2_Model

namespace SubsetShrink.L2

/-- Theorem 2, p. 14. For every ℓ2-regularized best-subsets solution `β̂₂` of (16) with data
`y = f* + ε`, under unit-norm columns, `σ > 0` and `1 ≤ k ≤ p`:

(A) Slow rate. If `λ ≥ [8 + 2√2] σ √(2k log(ep/k))`, then on `E_2k`,
`‖f* − Xβ̂₂‖² ≤ ‖f* − Xβ‖² + 2λ‖β‖` for every `β ∈ B0(k)`; and on `F` (any `δ0 ∈ (0, 1]`),
`‖f* − Xβ̂₂‖² ≤ C (‖f* − Xβ‖² + λ‖β‖ + σ² log(1/δ0))` for every `β ∈ B0(k)`.

(B) Fast rate. For every `λ ≥ 0` with `γ_2k > 0 ∨ λ = 0`, on `G_2k` (any `δ0 ∈ (0, 1]`),
`‖f* − Xβ̂₂‖² ≤ C (‖f* − Xβ‖² + σ²k log(ep/k) + γ_2k⁻² λ² + σ² log(1/δ0))` for every
`β ∈ B0(k)`.

Each `≲` is a universal constant `C > 0` chosen before all other data; the infimum over
`B0(k)` is the bound for every `β ∈ B0(k)`. -/
theorem theorem_2 :
    (∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (σ : ℝ) (k : ℕ)
        (lam : ℝ) (βhat : Fin p → ℝ),
      UnitCols X → 0 < σ → 1 ≤ k → k ≤ p →
      (8 + 2 * Real.sqrt 2) * σ *
        Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) ≤ lam →
      ε ∈ E X σ (2 * k) →
      IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat →
      ∀ β ∈ B0 k,
        l2 (resid X fstar βhat) ^ 2 ≤ l2 (resid X fstar β) ^ 2 + 2 * lam * l2 β) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (σ δ0 : ℝ) (k : ℕ)
        (lam : ℝ) (βhat : Fin p → ℝ),
      UnitCols X → 0 < σ → 1 ≤ k → k ≤ p → 0 < δ0 → δ0 ≤ 1 →
      (8 + 2 * Real.sqrt 2) * σ *
        Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) ≤ lam →
      ε ∈ F X σ δ0 →
      IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat →
      ∀ β ∈ B0 k,
        l2 (resid X fstar βhat) ^ 2 ≤
          C * (l2 (resid X fstar β) ^ 2 + lam * l2 β + σ ^ 2 * Real.log (1 / δ0))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (σ δ0 : ℝ) (k : ℕ)
        (lam : ℝ) (βhat : Fin p → ℝ),
      UnitCols X → 0 < σ → 1 ≤ k → k ≤ p → 0 < δ0 → δ0 ≤ 1 → 0 ≤ lam →
      (0 < gam X (2 * k) ∨ lam = 0) →
      ε ∈ G X σ δ0 (2 * k) →
      IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat →
      ∀ β ∈ B0 k,
        l2 (resid X fstar βhat) ^ 2 ≤
          C * (l2 (resid X fstar β) ^ 2 +
            σ ^ 2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ)) +
            lam ^ 2 / gam X (2 * k) ^ 2 + σ ^ 2 * Real.log (1 / δ0))) := by sorry

end SubsetShrink.L2
