-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_proposition_1
-- name    : SDPT3.ScaleInv.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:18.491984+00:00
-- url     : https://prove2.me/theorems/5ba9265a-3977-4176-82fc-374536700fdc
-- title:
--   Proposition 1, p. 11 — for a pure SOCP, the HKM and NT directions are invariant under automorphic scaling of the cones
-- statement:
--   Consider a pure second-order cone program (no semidefinite or linear blocks) with blocks $i = 1, \dots, n_q$ of dimensions $q_i$, data $A_i \in \mathbb R^{q_i\times m}$, $b \in \mathbb R^m$, $c_i \in \mathbb R^{q_i}$, an iterate $(x, y, z)$ with every $x_i$ and $z_i$ in the interior of the second-order cone, and a centering parameter $\sigma$. Fix the search direction to be either HKM or NT. For each block let $F_i$ be an automorphism of the cone $K_q^{q_i}$, and form the scaled problem and iterate
--   $$\hat A_i = F_i^{-1}A_i,\quad \hat b = b,\quad \hat c_i = F_i^{-1}c_i,\quad \hat x_i = F_i^\top x_i,\quad \hat y = y,\quad \hat z_i = F_i^{-1}z_i.$$
--   Then, for every $(\Delta x, \Delta y, \Delta z)$,
--   $$(\Delta x, \Delta y, \Delta z) \text{ solves (4) for the original data} \iff (F^\top\Delta x,\ \Delta y,\ F^{-1}\Delta z) \text{ solves (4) for the scaled data},$$
--   where $F^\top \Delta x$ and $F^{-1}\Delta z$ act block by block.
--
--   In words: the HKM and NT search directions are **scale-invariant** — the direction computed for the scaled problem is exactly the image of the original direction under the scaling. This is Proposition 1 of the paper.
--
--   **Formalization Note** The automorphism group $\mathcal G_i$ is encoded algebraically: $F_i^\top \bar J F_i = \lambda^2 \bar J$ for some $\lambda > 0$ and $(F_i)_{00} > 0$. The theorem covers all of $\mathcal G_i$, including $\lambda \ne 1$; the paper's (31) and its remark that $\omega$ is unchanged hold only for $\lambda = 1$ (printed slip), but the proposition itself holds for every $\lambda > 0$. The direction is characterized by the raw Newton system (4) with $\mathcal E, \mathcal F$ from (8) and $G$ from (19)/(21), and the conclusion is stated for the solution sets, so no uniqueness is needed and the paper's assumption that $A$ has full row rank (p. 5) is not used. Interiority of the scaled iterate is not assumed; it follows from $F_i \in \mathcal G_i$. Block vectors are `Fin (d i + 1) → ℝ`, with $x_i^0$ at index `0` and $x_i^1$ at the indices `Fin.succ j`; the interior is encoded by $x_i^0 > 0$ and $(x_i^0)^2 - \langle x_i^1, x_i^1\rangle > 0$.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 11, Proposition 1; proof p. 12

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem proposition_1 {nq m : ℕ} {d : Fin nq → ℕ} (dir : Dir)
    (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ) (b : Fin m → ℝ)
    (c x : (i : Fin nq) → Fin (d i + 1) → ℝ) (y : Fin m → ℝ)
    (z : (i : Fin nq) → Fin (d i + 1) → ℝ) (σ : ℝ)
    (hx : ∀ i, socInt (x i)) (hz : ∀ i, socInt (z i))
    (Fsc : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin (d i + 1)) ℝ) (hF : ∀ i, IsSOCAut (Fsc i))
    (Δx : (i : Fin nq) → Fin (d i + 1) → ℝ) (Δy : Fin m → ℝ)
    (Δz : (i : Fin nq) → Fin (d i + 1) → ℝ) :
    IsNewtonDir dir A b c x y z σ Δx Δy Δz ↔
      IsNewtonDir dir (fun i => (Fsc i)⁻¹ * A i) b (fun i => (Fsc i)⁻¹ *ᵥ c i)
        (fun i => (Fsc i)ᵀ *ᵥ x i) y (fun i => (Fsc i)⁻¹ *ᵥ z i) σ
        (fun i => (Fsc i)ᵀ *ᵥ Δx i) Δy (fun i => (Fsc i)⁻¹ *ᵥ Δz i) := by sorry

end SDPT3.ScaleInv
