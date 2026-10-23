-- Prove2me | Theorems.Thm_ShannoCG1978_eq27_scaled_direction_exact_faithful
-- name    : ShannoCG1978.eq27_scaled_direction_exact_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:36:09.618116+00:00
-- url     : https://prove2.me/theorems/a94fe642-4574-4f93-9e05-5f5674709dd9
-- title:
--   Eq. (27): under an exact search the self-scaled direction is $\gamma$ times the unscaled one
-- statement:
--   Let $p_k, y_k, g_{k+1} \in \mathbb R^n$ with $p_k'y_k > 0$, let $\gamma = p_k'y_k / y_k'y_k$, and let
--
--   $$H = \gamma\Big(I - \frac{p_k y_k' + y_k p_k'}{p_k'y_k} + \frac{y_k'y_k}{p_k'y_k}\,\frac{p_k p_k'}{p_k'y_k}\Big) + \frac{p_k p_k'}{p_k'y_k}$$
--
--   be the BFGS update of $\gamma I$ with $(p_k, y_k)$, so that $d_{k+1} = -Hg_{k+1}$ is the self-scaled direction (26)–(26a). If the search is exact, $p_k'g_{k+1} = 0$, then
--
--   $$d_{k+1} = \gamma\Big(-g_{k+1} + \frac{y_k'g_{k+1}}{p_k'y_k}\,p_k\Big).$$
--
--   This is eq. (27) of Shanno (1978), §III: scaling only changes the length of the search direction, so $n$-step convergence on a quadratic is kept. It is the one-update analogue of the goal theorem of the existing mission (the double update reduces to $\gamma_t$ times Beale's direction).
--
--   **Formalization Note** $H$ is the platform's `scaledRestart` (the matrix of (37)), which coincides with the scaled matrix of (26) built from $(p_k, y_k)$; $p_k'y_k > 0$ is the paper's standing search-length criterion.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, doi:10.1287/moor.3.3.244, §III, p. 248, eqs. (26a)–(27)

import Mathlib
import Definitions.Def_ShannoCG_SCONB_gammaScale
import Definitions.Def_ShannoCG_SCONB_scaledRestart

open Matrix ShannoCG.SCONB

theorem ShannoCG1978.eq27_scaled_direction_exact_faithful {n : ℕ} (p y g : Fin n → ℝ)
    (hpy : 0 < p ⬝ᵥ y) (hexact : p ⬝ᵥ g = 0) :
    -(scaledRestart p y *ᵥ g) = gammaScale p y • (-g + ((y ⬝ᵥ g) / (p ⬝ᵥ y)) • p) := by sorry
