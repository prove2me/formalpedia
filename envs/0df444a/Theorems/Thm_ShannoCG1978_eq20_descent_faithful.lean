-- Prove2me | Theorems.Thm_ShannoCG1978_eq20_descent_faithful
-- name    : ShannoCG1978.eq20_descent_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:36:09.704345+00:00
-- url     : https://prove2.me/theorems/2a90a9a2-040f-451b-b833-d476f01f9b57
-- title:
--   The memoryless BFGS direction (20) is a descent direction when $p_k'y_k > 0$
-- statement:
--   Let $p_k, y_k \in \mathbb R^n$ with $p_k'y_k > 0$, let $Q^*_{k+1}$ be the BFGS update (16) of the identity with $(p_k, y_k)$, as in (18), and let $g_{k+1} \ne 0$. Then the direction $d_{k+1} = -Q^*_{k+1}g_{k+1}$ of (19)–(20) is a descent direction:
--
--   $$g_{k+1}'d_{k+1} < 0.$$
--
--   This is the stability remark of Shanno (1978), §II, p. 247, which follows from the positive definiteness of the BFGS update when $p_k'y_k > 0$. It is the one-update analogue of the descent property of the double-update direction (34), a milestone of the existing mission.
--
--   **Formalization Note** The hypothesis $g_{k+1} \ne 0$ excludes the stationary point, where the direction is zero.
-- source:
--   Shanno, Conjugate Gradient Methods with Inexact Searches, Math. Oper. Res. 3(3) (1978) 244–256, doi:10.1287/moor.3.3.244, §II, p. 247

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bfgsUpdate

open Matrix ShannoCG.SCONB

theorem ShannoCG1978.eq20_descent_faithful {n : ℕ} (p y g : Fin n → ℝ)
    (hpy : 0 < p ⬝ᵥ y) (hg : g ≠ 0) :
    g ⬝ᵥ (-(bfgsUpdate (1 : Matrix (Fin n) (Fin n) ℝ) p y *ᵥ g)) < 0 := by sorry
