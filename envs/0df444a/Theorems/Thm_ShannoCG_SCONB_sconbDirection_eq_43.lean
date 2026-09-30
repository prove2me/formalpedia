-- Prove2me | Theorems.Thm_ShannoCG_SCONB_sconbDirection_eq_43
-- name    : ShannoCG.SCONB.sconbDirection_eq_43
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T07:33:33.090713+00:00
-- url     : https://prove2.me/theorems/4a327bbd-801a-4929-ab39-144faaf7823a
-- title:
--   Eq. (43): the self-scaled direction under the three orthogonalities
-- statement:
--   Let $p_t, y_t, p_k, y_k, g_{k+1} \in \mathbb R^n$ with $p_t'y_t \ne 0$, and let $d_{k+1} = -\hat H_{k+1} g_{k+1}$ be the self-scaled two-update direction ($\hat H_k$ from (37), $\hat H_{k+1}$ its BFGS update with $(p_k, y_k)$). Assume
--
--   1. $p_k' g_{k+1} = 0$ (exact search at step $k$);
--   2. $p_t' g_{k+1} = 0$;
--   3. $y_k' p_t = 0$ (conjugacy).
--
--   Then
--
--   $$d_{k+1} = -\frac{p_t' y_t}{y_t' y_t}\, g_{k+1} + \frac{y_t' g_{k+1}}{y_t' y_t}\, p_t + \frac{y_k' g_{k+1}}{p_k' y_k}\,\frac{p_t' y_t}{y_t' y_t}\, p_k.$$
--
--   This is the algebraic core of Shanno's reduction: once the three orthogonalities hold, the self-scaled direction is an explicit combination of $g_{k+1}$, $p_t$ and $p_k$.
--
--   **Formalization Note** Stated for arbitrary vectors. No condition on $p_k'y_k$ is needed, since both sides use the same quotient.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, DOI 10.1287/moor.3.3.244, p. 251 (PDF p. 8), §IV, eq. (43)

import Mathlib
import Definitions.Def_ShannoCG_SCONB_gammaScale
import Definitions.Def_ShannoCG_SCONB_sconbDirection

open Matrix

namespace ShannoCG.SCONB

/-- Shanno, *Conjugate Gradient Methods with Inexact Searches*, Math. Oper. Res. 3(3) (1978), §IV, p. 251 (PDF 8), eq. (43): if `p_k' g_{k+1} = 0`, `p_t' g_{k+1} = 0` and
`y_k' p_t = 0`, the self-scaled two-update direction is
`d_{k+1} = −(p_t'y_t / y_t'y_t) g_{k+1} + (y_t'g_{k+1} / y_t'y_t) p_t
  + (y_k'g_{k+1} / p_k'y_k)(p_t'y_t / y_t'y_t) p_k`.

**Formalization Note.** Stated generically (`g` plays `g_{k+1}`). The three orthogonalities are
hypotheses: exact search at `k`, the fact M4 (`p_t'g_{k+1} = 0`) and the conjugacy `y_k'p_t = 0`.
`p_t ⬝ᵥ y_t ≠ 0` keeps (37) genuine; no condition on `p_k ⬝ᵥ y_k` is needed since both sides
use the same quotient. -/
theorem sconbDirection_eq_43 {n : ℕ} (pt yt pk yk g : Fin n → ℝ) (hpy : pt ⬝ᵥ yt ≠ 0)
    (hexact_k : pk ⬝ᵥ g = 0) (horth : pt ⬝ᵥ g = 0) (hconj : yk ⬝ᵥ pt = 0) :
    sconbDirection pt yt pk yk g =
      -(gammaScale pt yt • g) + ((yt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • pt
        + ((yk ⬝ᵥ g) / (pk ⬝ᵥ yk) * gammaScale pt yt) • pk := by sorry

end ShannoCG.SCONB
