-- Prove2me | Theorems.Thm_ShannoCG_SCONB_bfgsUpdate_mulVec_of_exact
-- name    : ShannoCG.SCONB.bfgsUpdate_mulVec_of_exact
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:10:52.213619+00:00
-- url     : https://prove2.me/theorems/87d878f2-3dc7-427e-92e1-04768517f384
-- title:
--   Eq. (40): the two-update direction under an exact search
-- statement:
--   Let $\hat H_k$ be any real $n\times n$ matrix, $p_k, y_k, g_{k+1} \in \mathbb R^n$, and $\hat H_{k+1}$ the BFGS update of $\hat H_k$ with $(p_k, y_k)$. If the line search at step $k$ is exact, i.e. $p_k' g_{k+1} = 0$, then
--
--   $$d_{k+1} = -\hat H_{k+1} g_{k+1} = -\hat H_k g_{k+1} + \frac{y_k' \hat H_k g_{k+1}}{p_k' y_k}\, p_k.$$
--
--   This is the first step of Shanno's reduction of the double-update methods to Beale's method: under exact searches only one correction term of the update survives.
--
--   **Formalization Note** Stated generically: $\hat H_k$ is arbitrary, $g$ plays the role of $g_{k+1}$ and the exact search is the hypothesis $p_k'g_{k+1} = 0$.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 251 (PDF p. 8), §IV, eq. (40)

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bfgsUpdate

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, p. 251 (PDF 8), eq. (40): under the exact-search condition `p_k' g_{k+1} = 0`, the
direction `d_{k+1} = −Ĥ_{k+1} g_{k+1}` (with `Ĥ_{k+1}` the update (32) of `Ĥ_k`) equals
`−Ĥ_k g_{k+1} + (y_k' Ĥ_k g_{k+1} / p_k' y_k) p_k`.

**Formalization Note.** Stated generically for any matrix `H` and vectors `p, y, g` (`g` plays
`g_{k+1}`); the exact search is the hypothesis `p ⬝ᵥ g = 0`. -/
theorem bfgsUpdate_mulVec_of_exact {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (p y g : Fin n → ℝ)
    (hexact : p ⬝ᵥ g = 0) :
    -(bfgsUpdate H p y *ᵥ g) = -(H *ᵥ g) + ((y ⬝ᵥ (H *ᵥ g)) / (p ⬝ᵥ y)) • p := by sorry

end ShannoCG.SCONB
