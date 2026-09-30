-- Prove2me | Theorems.Thm_ShannoCG_SCONB_bconDirection_descent
-- name    : ShannoCG.SCONB.bconDirection_descent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:41:35.324285+00:00
-- url     : https://prove2.me/theorems/f971ee5d-d977-435b-bb83-9cc24103de5a
-- title:
--   The unscaled two-update direction is a descent direction
-- statement:
--   Let $p_t, y_t, p_k, y_k, g_{k+1} \in \mathbb R^n$ with $p_t'y_t > 0$, $p_k'y_k > 0$ and $g_{k+1} \ne 0$, and let $d_{k+1} = -\hat H_{k+1} g_{k+1}$ be the unscaled two-update direction ($\hat H_k$ from (31), $\hat H_{k+1}$ its BFGS update (32) with $(p_k, y_k)$). Then
--
--   $$g_{k+1}'\, d_{k+1} < 0.$$
--
--   This is the same descent guarantee as for the self-scaled method, for the algorithm (34)–(36).
--
--   **Formalization Note** The curvature condition is assumed for both pairs $(p_t, y_t)$ and $(p_k, y_k)$; "descent direction" is read as $g_{k+1}'d_{k+1} < 0$ with $g_{k+1} \ne 0$.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 250 (PDF p. 7), §IV, the paragraph after eq. (39) (algorithm (34)–(36))

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bconDirection

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, p. 250 (PDF 7), the paragraph after (39): as the method uses two sequential
quasi-Newton updates, `p_k'y_k > 0` is sufficient to ensure that the search direction `d_{k+1}` is
always a descent direction. Stated here for the unscaled algorithm (34)–(36), i.e.
`d_{k+1} = −Ĥ_{k+1} g_{k+1}` with `Ĥ_k` from (31) and `Ĥ_{k+1}` from (32).

**Formalization Note.** "`p_k'y_k > 0`" is assumed for both pairs `(p_t, y_t)` and `(p_k, y_k)`.
"Descent direction" is `g_{k+1}' d_{k+1} < 0`, which requires `g_{k+1} ≠ 0`. Generic vectors. -/
theorem bconDirection_descent {n : ℕ} (pt yt pk yk g : Fin n → ℝ) (hpyt : 0 < pt ⬝ᵥ yt)
    (hpyk : 0 < pk ⬝ᵥ yk) (hg : g ≠ 0) :
    g ⬝ᵥ bconDirection pt yt pk yk g < 0 := by sorry

end ShannoCG.SCONB
