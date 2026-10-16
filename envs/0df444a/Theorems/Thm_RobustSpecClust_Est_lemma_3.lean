-- Prove2me | Theorems.Thm_RobustSpecClust_Est_lemma_3
-- name    : RobustSpecClust.Est.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:25.403846+00:00
-- url     : https://prove2.me/theorems/af3c74cc-dc7a-401e-aae3-a3eeef5f0b99
-- title:
--   Lemma 3, p. 13 — ⟨R − γE_N, X⁰ − X̂⟩ ≤ 2‖K_I − R_I‖₁
-- statement:
--   Let $K$ be a matrix indexed by the $N = n+m$ points, $R$ the reference matrix (6) built from $K$, $\varphi$, $\tau_{\mathrm{in}}$, $\tau^{(k,l)}_{\mathrm{out}}$ and $\gamma$, $X^0$ the true clustering matrix, and $\hat X$ the Robust-LP solution $\hat X_{ij} = \mathbb 1\{K_{ij} > \gamma\}$. Suppose the inlier blocks satisfy $K_{\mathcal I}, R_{\mathcal I} \in [0,1]^{n\times n}$. Then
--   $$\langle R - \gamma E_N, X^0 - \hat X\rangle \le 2\,\|K_{\mathcal I} - R_{\mathcal I}\|_1 .$$
--
--   If the kernel is close to the reference matrix in the entrywise $\ell_1$ norm, then $\hat X$ is nearly optimal for the reference problem. Combined with Lemma 2 this bounds the estimation error by $\|K_{\mathcal I} - R_{\mathcal I}\|_1$.
-- source:
--   arXiv:1912.07546v3, Lemma 3, p. 13; proof in Appendix D, p. 39

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem lemma_3 {n m r : ℕ} (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r) (τin : ℝ)
    (τout : Fin r → Fin r → ℝ) (γ : ℝ)
    (hK : ∀ i j, 0 ≤ inlierBlock K i j ∧ inlierBlock K i j ≤ 1)
    (hR : ∀ i j, 0 ≤ inlierBlock (refMatrix K φ τin τout γ) i j ∧
      inlierBlock (refMatrix K φ τin τout γ) i j ≤ 1) :
    frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (trueClust φ - robustLPSol K γ) ≤
      2 * l1 (inlierBlock K - inlierBlock (refMatrix K φ τin τout γ)) := by sorry

end RobustSpecClust.Est
