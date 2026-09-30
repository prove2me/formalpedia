-- Prove2me | Theorems.Thm_ShannoCG_SCONB_scaledRestart_mulVec_of_orth
-- name    : ShannoCG.SCONB.scaledRestart_mulVec_of_orth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:28:38.22918+00:00
-- url     : https://prove2.me/theorems/35c52140-ef51-4d6c-83a3-c198feedc9b0
-- title:
--   Eq. (42): the self-scaled restart matrix on a gradient orthogonal to $p_t$
-- statement:
--   Let $p_t, y_t, g_{k+1} \in \mathbb R^n$ with $p_t' y_t \ne 0$ and $p_t' g_{k+1} = 0$, and let $\hat H_k$ be the self-scaled restart matrix (37). Then
--
--   $$\hat H_k g_{k+1} = \frac{p_t' y_t}{y_t' y_t}\, g_{k+1} - \frac{y_t' g_{k+1}}{y_t' y_t}\, p_t.$$
--
--   Under exact searches on a quadratic the hypothesis $p_t'g_{k+1} = 0$ holds, and this simplified form is substituted into (40) to obtain the direction (43).
--
--   **Formalization Note** Stated generically, with $g$ in place of $g_{k+1}$.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 251 (PDF p. 8), §IV, eq. (42)

import Mathlib
import Definitions.Def_ShannoCG_SCONB_gammaScale
import Definitions.Def_ShannoCG_SCONB_scaledRestart

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, p. 251 (PDF 8), eq. (42): if `p_t' g_{k+1} = 0`, the self-scaled restart matrix (37)
satisfies `Ĥ_k g_{k+1} = (p_t'y_t / y_t'y_t) g_{k+1} − (y_t'g_{k+1} / y_t'y_t) p_t`.

**Formalization Note.** Stated generically (`g` plays `g_{k+1}`); `p_t ⬝ᵥ y_t ≠ 0` keeps the
quotients in (37) genuine. -/
theorem scaledRestart_mulVec_of_orth {n : ℕ} (pt yt g : Fin n → ℝ) (hpy : pt ⬝ᵥ yt ≠ 0)
    (horth : pt ⬝ᵥ g = 0) :
    scaledRestart pt yt *ᵥ g = gammaScale pt yt • g - ((yt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • pt := by sorry

end ShannoCG.SCONB
