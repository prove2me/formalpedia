-- Prove2me | Theorems.Thm_ShannoCG1978_eq20_memoryless_bfgs_direction_faithful
-- name    : ShannoCG1978.eq20_memoryless_bfgs_direction_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:36:07.636243+00:00
-- url     : https://prove2.me/theorems/d5141a07-e811-4f37-abe5-501b7c8d27bc
-- title:
--   Eq. (20): the memoryless BFGS direction $-Q^*_{k+1}g_{k+1}$ in matrix-free form
-- statement:
--   Let $p_k, y_k, g_{k+1} \in \mathbb R^n$ with $p_k'y_k > 0$, and let $Q^*_{k+1}$ be the BFGS update (16) of the identity matrix with the pair $(p_k, y_k)$, that is
--
--   $$Q^*_{k+1} = I - \frac{p_k y_k' + y_k p_k'}{y_k'p_k} + \Big(1 + \frac{y_k'y_k}{p_k'y_k}\Big)\frac{p_k p_k'}{p_k'y_k}.$$
--
--   Then the search direction $d_{k+1} = -Q^*_{k+1} g_{k+1}$ is
--
--   $$d_{k+1} = -g_{k+1} - \Big(\Big(1 + \frac{y_k'y_k}{p_k'y_k}\Big)\frac{p_k'g_{k+1}}{p_k'y_k} - \frac{y_k'g_{k+1}}{p_k'y_k}\Big)p_k + \frac{p_k'g_{k+1}}{p_k'y_k}\,y_k.$$
--
--   This is eq. (20) of Shanno (1978), §II: the conjugate gradient method obtained from the BFGS method by restarting the inverse Hessian approximation at the identity at every step needs no stored matrix.
--
--   **Formalization Note** The BFGS update of $I$ is the platform's `bfgsUpdate` applied to the identity matrix; $p_k'y_k > 0$ is the paper's search-length criterion and makes every denominator nonzero.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, doi:10.1287/moor.3.3.244, §II, p. 246, eqs. (18)–(20)

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bfgsUpdate

open Matrix ShannoCG.SCONB

theorem ShannoCG1978.eq20_memoryless_bfgs_direction_faithful {n : ℕ} (p y g : Fin n → ℝ)
    (hpy : 0 < p ⬝ᵥ y) :
    -(bfgsUpdate (1 : Matrix (Fin n) (Fin n) ℝ) p y *ᵥ g) =
      -g - ((1 + (y ⬝ᵥ y) / (p ⬝ᵥ y)) * ((p ⬝ᵥ g) / (p ⬝ᵥ y)) - (y ⬝ᵥ g) / (p ⬝ᵥ y)) • p
        + ((p ⬝ᵥ g) / (p ⬝ᵥ y)) • y := by sorry
