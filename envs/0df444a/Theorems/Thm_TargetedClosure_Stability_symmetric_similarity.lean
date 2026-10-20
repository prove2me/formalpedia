-- Prove2me | Theorems.Thm_TargetedClosure_Stability_symmetric_similarity
-- name    : TargetedClosure.Stability.symmetric_similarity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:07.435169+00:00
-- url     : https://prove2.me/theorems/5911f0d6-4062-4142-b70f-a426b33abc8a
-- title:
--   Proof of Lemma 2.1 — diagonal similarity to a symmetric matrix
-- statement:
--   Let $T=(\tau_{ij})$, $X=\operatorname{diag}(x_i)$, $\Lambda=\operatorname{diag}((\sum_lN_l\tau_{lk})^{-1})$, and $\widehat N=\operatorname{diag}(N_i)$. The reduced matrix of equation (8) satisfies
--
--   $$
--   \overline F(x)=\widehat N T X\Lambda T^{\mathsf T},\qquad
--   \widehat N^{-1/2}\overline F(x)\widehat N^{1/2}
--   =\widehat N^{1/2}TX\Lambda T^{\mathsf T}\widehat N^{1/2}.
--   $$
--
--   The matrix on the right is symmetric and has the same spectral radius as $\overline F(x)$. This identifies the symmetric representative used to convert the spectral bound to a positive-definiteness bound.
--
--   **Formalization Note** Every $N_i$ is positive, so the diagonal square root and its reciprocal are defined.
-- source:
--   Birge, Candogan & Feng, Controlling Epidemic Spread: Reducing Economic Losses with Targeted Closures, BFI Working Paper No. 2020-57 (May 18, 2020, preliminary), pp. 13–14 (PDF 14–15), proof of Lemma 2.1 after equation (8)

import Mathlib
import Definitions.Def_TargetedClosure_Stability_Model

namespace TargetedClosure.Stability

theorem symmetric_similarity {n : ℕ} (P : Params n) (hP : P.Standing)
    (x : Fin n → ℝ) (hx : IsActivity x) :
    Fbar P x = Nhat P * Tmat P * Xmat x * Lam P * (Tmat P).transpose ∧
    Nsqrtinv P * (Nhat P * Tmat P * Xmat x * Lam P * (Tmat P).transpose) * Nsqrt P =
      Nsqrt P * Tmat P * Xmat x * Lam P * (Tmat P).transpose * Nsqrt P ∧
    (Nsqrt P * Tmat P * Xmat x * Lam P * (Tmat P).transpose * Nsqrt P).IsSymm ∧
    spectrum ℂ ((Fbar P x).map (algebraMap ℝ ℂ)) =
      spectrum ℂ ((Nsqrt P * Tmat P * Xmat x * Lam P *
        (Tmat P).transpose * Nsqrt P).map (algebraMap ℝ ℂ)) ∧
    lam1 (Fbar P x) =
      lam1 (Nsqrt P * Tmat P * Xmat x * Lam P * (Tmat P).transpose * Nsqrt P) := by sorry

end TargetedClosure.Stability
