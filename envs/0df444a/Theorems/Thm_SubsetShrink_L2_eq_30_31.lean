-- Prove2me | Theorems.Thm_SubsetShrink_L2_eq_30_31
-- name    : SubsetShrink.L2.eq_30_31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:30.228243+00:00
-- url     : https://prove2.me/theorems/aefed7ca-912f-4b41-aca9-3879cb9c0fe5
-- title:
--   (30)–(31), p. 39 — on E_2k, the cross term is controlled and the first slow-rate bound holds
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, let $\sigma>0$, $1\le k\le p$, $f^*,\epsilon\in\mathbb R^n$ and $y=f^*+\epsilon$. Suppose
--   $$\lambda\ge[8+2\sqrt2]\,\sigma\sqrt{2k\log(ep/k)},$$
--   that $\epsilon$ lies in the event $\mathcal E_{2k}$, and that $\hat\beta_2$ is any $\ell_2$-regularized best-subsets solution of (16). Then for every $\beta\in B_0(k)$:
--
--   1. (30) $\displaystyle \epsilon^\top X(\hat\beta_2-\beta)\le[4+\sqrt2]\,\sigma\sqrt{2k\log(ep/k)}\,\|\beta-\hat\beta_2\|$;
--   2. (31) $\displaystyle \|f^*-X\hat\beta_2\|^2\le\|f^*-X\beta\|^2+2\lambda\|\beta\|$.
--
--   Part 2 is the first slow-rate bound of Theorem 2(A), for each comparison vector $\beta$.
--
--   **Formalization Note** $\mathcal E_{2k}$ is the event $\mathcal E_s$ of p. 13 at $s=2k$, whose threshold $s\log(2ep/s)$ equals $2k\log(ep/k)$ there. The standing hypotheses of §3.1 (unit columns, $\sigma>0$) and the model-size range $1\le k\le p$ are carried as binders.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 39, proof of Theorem 2 (B.2), (30)–(31)

import Mathlib
import Definitions.Def_SubsetShrink_L2_Model

namespace SubsetShrink.L2

/-- Proof of Theorem 2 (B.2), p. 39, (30)–(31): if `λ ≥ [8 + 2√2] σ √(2k log(ep/k))`, then on
the event `E_2k`, for every ℓ2-regularized best-subsets solution `βhat` (16) with data
`y = f* + ε` and every `β ∈ B0(k)`,
(30) `ε⊤X(β̂₂ − β) ≤ [4 + √2] σ √(2k log(ep/k)) ‖β − β̂₂‖`, and
(31) `‖f* − Xβ̂₂‖² ≤ ‖f* − Xβ‖² + 2λ‖β‖`.
`E_2k` is the event `E_s` of p. 13 at `s = 2k`; its radicand `s log(2ep/s)` equals
`2k log(ep/k)` there. -/
theorem eq_30_31 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ)
    (σ : ℝ) (k : ℕ) (lam : ℝ) (βhat β : Fin p → ℝ)
    (hX : UnitCols X) (hσ : 0 < σ) (hk : 1 ≤ k) (hkp : k ≤ p)
    (hlam : (8 + 2 * Real.sqrt 2) * σ *
      Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) ≤ lam)
    (hE : ε ∈ E X σ (2 * k))
    (hbest : IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat) (hβ : β ∈ B0 k) :
    dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ *
          Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) *
            l2 (β - βhat) ∧
      l2 (resid X fstar βhat) ^ 2 ≤ l2 (resid X fstar β) ^ 2 + 2 * lam * l2 β := by sorry

end SubsetShrink.L2
