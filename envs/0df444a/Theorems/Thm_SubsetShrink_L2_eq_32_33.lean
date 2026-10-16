-- Prove2me | Theorems.Thm_SubsetShrink_L2_eq_32_33
-- name    : SubsetShrink.L2.eq_32_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:29.657714+00:00
-- url     : https://prove2.me/theorems/5e5f6fc3-9f40-4c08-b3e8-d31b967b2d7e
-- title:
--   (30)–(33), p. 39 — on F, either (30) implies (31) or (32) implies (33)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, let $\sigma>0$, $\delta_0\in(0,1]$, $1\le k\le p$, $\lambda\ge[8+2\sqrt2]\sigma\sqrt{2k\log(ep/k)}$, $f^*,\epsilon\in\mathbb R^n$ and $y=f^*+\epsilon$. Suppose $\epsilon$ lies in the event $\mathcal F$ (with parameter $\delta_0$) and $\hat\beta_2$ is any $\ell_2$-regularized best-subsets solution of (16). Then for every $\beta\in B_0(k)$:
--
--   1. either (30) $\displaystyle \epsilon^\top X(\hat\beta_2-\beta)\le[4+\sqrt2]\,\sigma\sqrt{2k\log(ep/k)}\,\|\beta-\hat\beta_2\|$, or (32) $\displaystyle \epsilon^\top X(\hat\beta_2-\beta)\le[4+\sqrt2]\,\sigma\sqrt{\log(1/\delta_0)}\,\|X(\beta-\hat\beta_2)\|$;
--   2. if (30) holds, then (31) $\|f^*-X\hat\beta_2\|^2\le\|f^*-X\beta\|^2+2\lambda\|\beta\|$;
--   3. if (32) holds, then (33)
--   $$\|f^*-X\hat\beta_2\|^2\le\|f^*-X\beta\|^2+\lambda\|\beta\|+2[4+\sqrt2]\,\sigma\sqrt{\log(1/\delta_0)}\,\big(\|f^*-X\hat\beta_2\|+\|f^*-X\beta\|\big).$$
--
--   This dichotomy is the deterministic core of the second slow-rate bound of Theorem 2(A): in case (30) the first slow-rate bound applies, and in case (32) inequality (33) is turned into the bound with the additive term $\sigma^2\log(1/\delta_0)$.
--
--   **Formalization Note** The standing hypotheses of §3.1, $1\le k\le p$, and the slow-rate penalty threshold from Theorem 2(A) are binders. Both alternatives and implications are stated for the same $\beta$.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 39, proof of Theorem 2 (B.2), (32)–(33)

import Mathlib
import Definitions.Def_SubsetShrink_L2_Model

namespace SubsetShrink.L2

/-- Proof of Theorem 2 (B.2), p. 39, (32)–(33): on the event `F` (with parameter
`δ0 ∈ (0, 1]`), for every ℓ2-regularized best-subsets solution `βhat` (16) with data
`y = f* + ε`, `λ ≥ [8 + 2√2] σ √(2k log(ep/k))`, and every `β ∈ B0(k)`, either
(a) (30) `ε⊤X(β̂₂ − β) ≤ [4 + √2] σ √(2k log(ep/k)) ‖β − β̂₂‖`, or
(b) (32) `ε⊤X(β̂₂ − β) ≤ [4 + √2] σ √log(1/δ0) ‖X(β − β̂₂)‖`;
 (30) implies (31) `‖f* − Xβ̂₂‖² ≤ ‖f* − Xβ‖² + 2λ‖β‖`, and (32) implies (33)
`‖f* − Xβ̂₂‖² ≤ ‖f* − Xβ‖² + λ‖β‖ + 2[4 + √2] σ √log(1/δ0) (‖f* − Xβ̂₂‖ + ‖f* − Xβ‖)`. -/
theorem eq_32_33 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ)
    (σ δ0 : ℝ) (k : ℕ) (lam : ℝ) (βhat β : Fin p → ℝ)
    (hX : UnitCols X) (hσ : 0 < σ) (hk : 1 ≤ k) (hkp : k ≤ p)
    (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1)
    (hlam : (8 + 2 * Real.sqrt 2) * σ *
      Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) ≤ lam)
    (hF : ε ∈ F X σ δ0)
    (hbest : IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat) (hβ : β ∈ B0 k) :
        (dot ε (X.mulVec (βhat - β)) ≤
            (4 + Real.sqrt 2) * σ *
              Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) *
                l2 (β - βhat) ∨
          dot ε (X.mulVec (βhat - β)) ≤
            (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec (β - βhat))) ∧
        (dot ε (X.mulVec (βhat - β)) ≤
            (4 + Real.sqrt 2) * σ *
              Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) *
                l2 (β - βhat) →
          l2 (resid X fstar βhat) ^ 2 ≤
            l2 (resid X fstar β) ^ 2 + 2 * lam * l2 β) ∧
    (dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec (β - βhat)) →
      l2 (resid X fstar βhat) ^ 2 ≤
        l2 (resid X fstar β) ^ 2 + lam * l2 β +
          2 * (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (1 / δ0)) *
            (l2 (resid X fstar βhat) + l2 (resid X fstar β))) := by sorry

end SubsetShrink.L2
