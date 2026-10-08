-- Prove2me | Theorems.Thm_ResolvingNRM_FRUpper_fr_dlp_gap_explicit
-- name    : ResolvingNRM.FRUpper.fr_dlp_gap_explicit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:44:05.283746+00:00
-- url     : https://prove2.me/theorems/2d0f4d71-9726-4673-9566-b0112fca137a
-- title:
--   p. 36 — v^DLP − v^FR ≤ Σ_l r^l_max K_l (2√T + √2) + n r_max (log T + 1) + n r_max λ_max
-- statement:
--   Consider the network revenue management model with Poisson rates $\lambda_j > 0$, revenues $r_j \ge 0$, nonnegative consumption matrix $A = (a_{lj})$, initial capacity $C \ge 0$, and an integer horizon $T \ge 1$. Let $v^{\mathrm{DLP}} = T\, v(C/T)$ be the DLP value and $v^{\mathrm{FR}}$ the expected revenue of the FR policy (Algorithm 2) with any optimal-solution selector. With $r^l_{\max} = \max_j \{ r_j \mathbb{I}(a_{lj} > 0)/a_{lj} \}$, $K_l = \sqrt{\sum_j a_{lj}^2 \lambda_j}$, $r_{\max} = \max_j r_j$ and $\lambda_{\max} = \max_j \lambda_j$,
--   $$v^{\mathrm{DLP}} - v^{\mathrm{FR}} \ \le\ \sum_{l=1}^m r^l_{\max} K_l \big(2\sqrt{T} + \sqrt{2}\big) + n\, r_{\max} (\log T + 1) + n\, r_{\max} \lambda_{\max} .$$
--
--   This is the explicit form of Proposition 3: every constant depends on $\lambda$, $r$ and $A$ only, and none on the capacity $C$.
--
--   **Formalization Note.** The bound is the last display of the proof of Proposition 3 (p. 36) with the constant $K_l$ of Lemma 8 corrected from $\sqrt{\sum_j a_{lj}^2\lambda_j^2}$ to $\sqrt{\sum_j a_{lj}^2\lambda_j}$ (see the Lemma 8 item; the printed constant is false). The printed sum over $l = 1, \dots, L$ is read as $l \in [m]$. $\log$ is the natural logarithm. $\lambda_j > 0$, $r \ge 0$, $a_{lj} \ge 0$, $C \ge 0$ are the model's standing assumptions (p. 7).
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, App. C.2, final display of the proof of Proposition 3, p. 36

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.FRUpper

/-- The explicit bound at the end of the proof of Proposition 3, App. C.2, p. 36, with the
corrected Lemma 8 constant `K_l = √(∑_j a_lj² λ_j)`:
`v^DLP − v^FR ≤ ∑_l r^l_max K_l (2√T + √2) + n r_max (log T + 1) + n r_max λ_max`. -/
theorem fr_dlp_gap_explicit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : 0 ≤ r) (hA : ∀ l j, 0 ≤ A l j)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (hsel : ResolvingNRM.IRT.IsDLPSelector A r lam sel)
    (T : ℕ) (hT : 1 ≤ T) (C : Fin m → ℝ) (hC : 0 ≤ C) :
    ResolvingNRM.IRT.dlpValue A r lam T C - frValue A r lam sel T C
      ≤ (∑ l, rmaxRes A r l * Kres A lam l) * (2 * Real.sqrt T + Real.sqrt 2)
        + n * rMax r * (Real.log T + 1) + n * rMax r * lamMax lam := by sorry

end ResolvingNRM.FRUpper
