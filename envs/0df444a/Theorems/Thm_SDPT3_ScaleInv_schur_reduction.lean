-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_schur_reduction
-- name    : SDPT3.ScaleInv.schur_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:12.045533+00:00
-- url     : https://prove2.me/theorems/5b15df26-51cc-434c-961a-f58b48d3e2d9
-- title:
--   (10)–(15), pp. 6–7 — for a pure SOCP, (4) is equivalent to M∆y = h, ∆z = R_d − Aᵀ∆y, ∆x = ℰ⁻¹R_c − ℰ⁻¹ℱ∆z
-- statement:
--   Consider a pure second-order cone program with blocks $i = 1, \dots, n_q$, data $A_i \in \mathbb R^{q_i\times m}$, $b$, $c_i$, an iterate $(x, y, z)$ with every $x_i$ and $z_i$ in the interior of the second-order cone, a centering parameter $\sigma$, and either the HKM or the NT scaling $G_i$. Let $\mathcal E_i, \mathcal F_i$ be as in (8), $R_d, r_p, R_c$ the residuals of (4), and
--   $$M = \sum_i A_i^\top \mathcal E_i^{-1}\mathcal F_i A_i,\qquad h = r_p - \sum_i A_i^\top \mathcal E_i^{-1}\big((R_c)_i - \mathcal F_i (R_d)_i\big)$$
--   as in (11)–(12). Then $(\Delta x, \Delta y, \Delta z)$ solves the Newton system (4) if and only if
--   $$M\Delta y = h \quad (10),\qquad \Delta z_i = (R_d)_i - A_i\Delta y \quad (13),\qquad \Delta x_i = \mathcal E_i^{-1}(R_c)_i - \mathcal E_i^{-1}\mathcal F_i \Delta z_i \quad (15)$$
--   for every block $i$.
--
--   This is the Schur-complement reduction by which SDPT3 computes its search direction, specialized to the pure second-order cone case.
--
--   **Formalization Note** The semidefinite and linear rows (14), (16) are absent because $n_s = n_l = 0$. The paper's standing assumption that $A$ has full row rank (p. 5) is not needed for the equivalence and is not assumed. Interiority of $x_i, z_i$ is the standing assumption of the algorithm; it guarantees that every $\mathcal E_i$ is invertible.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, pp. 6–7, (10)–(13), (15)

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem schur_reduction {nq m : ℕ} {d : Fin nq → ℕ} (dir : Dir)
    (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ) (b : Fin m → ℝ)
    (c x : (i : Fin nq) → Fin (d i + 1) → ℝ) (y : Fin m → ℝ)
    (z : (i : Fin nq) → Fin (d i + 1) → ℝ) (σ : ℝ)
    (hx : ∀ i, socInt (x i)) (hz : ∀ i, socInt (z i))
    (Δx : (i : Fin nq) → Fin (d i + 1) → ℝ) (Δy : Fin m → ℝ)
    (Δz : (i : Fin nq) → Fin (d i + 1) → ℝ) :
    IsNewtonDir dir A b c x y z σ Δx Δy Δz ↔
      (schurM dir A x z *ᵥ Δy = schurH dir A b c x y z σ ∧
        (∀ i, Δz i = Rd A c z y i - A i *ᵥ Δy) ∧
        (∀ i, Δx i = (calE (Gdir dir (x i) (z i)) (z i))⁻¹ *ᵥ Rc dir σ x z i -
          ((calE (Gdir dir (x i) (z i)) (z i))⁻¹ * calF (Gdir dir (x i) (z i)) (x i)) *ᵥ Δz i)) := by sorry

end SDPT3.ScaleInv
