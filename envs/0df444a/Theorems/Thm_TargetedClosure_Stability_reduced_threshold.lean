-- Prove2me | Theorems.Thm_TargetedClosure_Stability_reduced_threshold
-- name    : TargetedClosure.Stability.reduced_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:16.042675+00:00
-- url     : https://prove2.me/theorems/736b3db5-3803-4ca4-8e89-2b550d18e41f
-- title:
--   Proof of Lemma 2.1, equation (8) — reduced spectral threshold
-- statement:
--   Let $\mathcal R_e=\lambda_1(F(x)V^{-1})$, and define $\overline F(x)_{ij}=N_i\sum_k\tau_{ik}x_k\tau_{jk}/\sum_lN_l\tau_{lk}$. Under the model assumptions,
--
--   $$
--   \mathcal R_e<1\quad\Longleftrightarrow\quad
--   \lambda_1(\overline F(x))<
--   \frac{(\mu+\kappa)(\mu+\gamma)}{(\rho+\alpha(1-\rho))\beta\kappa}.
--   $$
--
--   This is the spectral condition immediately preceding the symmetric-matrix reformulation.
--
--   **Formalization Note** The threshold is positive under the standing assumptions; Lean compares the extended nonnegative spectral radius with its image as an extended nonnegative real.
-- source:
--   Birge, Candogan & Feng, Controlling Epidemic Spread: Reducing Economic Losses with Targeted Closures, BFI Working Paper No. 2020-57 (May 18, 2020, preliminary), p. 13 (PDF 14), proof of Lemma 2.1, equation (8)

import Mathlib
import Definitions.Def_TargetedClosure_Stability_Model

namespace TargetedClosure.Stability

theorem reduced_threshold {n : ℕ} (P : Params n) (hP : P.Standing)
    (x : Fin n → ℝ) (hx : IsActivity x) :
    Re P x < 1 ↔ lam1 (Fbar P x) < ENNReal.ofReal (thr P) := by sorry

end TargetedClosure.Stability
