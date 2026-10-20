-- Prove2me | Theorems.Thm_TargetedClosure_Stability_matrix_seven
-- name    : TargetedClosure.Stability.matrix_seven
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:22.10261+00:00
-- url     : https://prove2.me/theorems/e2c13082-7987-4df8-86f4-ef439786317f
-- title:
--   Proof of Lemma 2.1, equation (7) — reduced nonzero spectrum
-- statement:
--   Let $F(x)$ and $V$ be the $3n\times3n$ infected-coordinate Jacobians, and let $\overline F(x)$ be the $n\times n$ matrix with entries $N_i\sum_k\tau_{ik}x_k\tau_{jk}/\sum_lN_l\tau_{lk}$. Under the model assumptions, $F(x)V^{-1}$ and the matrix in equation (7) have the same nonzero complex eigenvalues:
--
--   $$
--   \operatorname{spec}(F(x)V^{-1})\setminus\{0\}=
--   \operatorname{spec}\!\left(\frac{(\rho+\alpha(1-\rho))\beta\kappa}{(\mu+\kappa)(\mu+\gamma)}\,\overline F(x)\right)\setminus\{0\}.
--   $$
--
--   This identifies the smaller matrix that controls the nonzero spectral behavior of the full infected-coordinate system.
--
--   **Formalization Note** Both spectra are taken after complexifying the real matrices.
-- source:
--   Birge, Candogan & Feng, Controlling Epidemic Spread: Reducing Economic Losses with Targeted Closures, BFI Working Paper No. 2020-57 (May 18, 2020, preliminary), p. 13 (PDF 14), proof of Lemma 2.1, equation (7)

import Mathlib
import Definitions.Def_TargetedClosure_Stability_Model

namespace TargetedClosure.Stability

theorem matrix_seven {n : ℕ} (P : Params n) (hP : P.Standing)
    (x : Fin n → ℝ) (hx : IsActivity x) :
    (spectrum ℂ ((Fmat P x * (Vmat P)⁻¹).map (algebraMap ℝ ℂ)) \ {0}) =
      (spectrum ℂ (((((P.ρ + P.α * (1 - P.ρ)) * P.β * P.κ /
        ((P.μ + P.κ) * (P.μ + P.γ))) • Fbar P x).map (algebraMap ℝ ℂ))) \ {0}) := by sorry

end TargetedClosure.Stability
