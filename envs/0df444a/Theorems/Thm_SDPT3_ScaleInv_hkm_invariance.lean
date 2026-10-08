-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_hkm_invariance
-- name    : SDPT3.ScaleInv.hkm_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:27.882988+00:00
-- url     : https://prove2.me/theorems/15c11480-57f0-480e-a468-49bee09f4db8
-- title:
--   Proof of Proposition 1, p. 12 — HKM step: r̂_p = r_p, R̂_d = F⁻¹R_d, γ²(ẑ) = γ²(z), and each M_i, M and h are invariant
-- statement:
--   Consider a pure second-order cone program with data $A_i, b, c_i$, an iterate $(x, y, z)$ with every $x_i, z_i$ in the interior of the cone, and a centering parameter $\sigma$. For each block let $F_i$ satisfy $F_i^\top \bar J F_i = \bar J$ and $(F_i)_{00} > 0$, and form the scaled quantities of the proof,
--   $$\hat A_i = F_i^{-1} A_i,\quad \hat b = b,\quad \hat c_i = F_i^{-1} c_i,\quad \hat x_i = F_i^\top x_i,\quad \hat y = y,\quad \hat z_i = F_i^{-1} z_i.$$
--   Then, for the HKM scaling,
--   1. $\hat r_p = r_p$ and $(\hat R_d)_i = F_i^{-1}(R_d)_i$ for every $i$;
--   2. $\gamma^2(\hat z_i) = \gamma^2(z_i)$ for every $i$;
--   3. each block $\hat M_i$ of the scaled Schur complement matrix equals $M_i$, and so $\hat M = M$;
--   4. the scaled right-hand side equals the original one: $\hat h = h$.
--
--   These are the invariances from which the proof of Proposition 1 concludes, via (10), (13) and (15), that the HKM direction transforms as $\widehat{\Delta y} = \Delta y$, $\widehat{\Delta z} = F^{-1}\Delta z$, $\widehat{\Delta x} = F^\top \Delta x$.
--
--   **Formalization Note** The proof assumes (31), i.e. $F_i^\top \bar J F_i = \bar J$; this statement takes that printed hypothesis together with $(F_i)_{00} > 0$, which makes $F_i$ an automorphism of the cone (the case $\lambda = 1$ of $\mathcal G_i$). For $\lambda F_i$ with $\lambda \ne 1$, $\gamma^2(\hat z_i) = \gamma^2(z_i)/\lambda^2$ and this step needs restating; the goal theorem covers all of $\mathcal G_i$.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 12, proof of Proposition 1 (HKM part)

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem hkm_invariance {nq m : ℕ} {d : Fin nq → ℕ}
    (A : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin m) ℝ) (b : Fin m → ℝ)
    (c x : (i : Fin nq) → Fin (d i + 1) → ℝ) (y : Fin m → ℝ)
    (z : (i : Fin nq) → Fin (d i + 1) → ℝ) (σ : ℝ)
    (hx : ∀ i, socInt (x i)) (hz : ∀ i, socInt (z i))
    (Fsc : (i : Fin nq) → Matrix (Fin (d i + 1)) (Fin (d i + 1)) ℝ)
    (hF : ∀ i, (Fsc i)ᵀ * Jbar (d i) * Fsc i = Jbar (d i)) (hF0 : ∀ i, 0 < Fsc i 0 0) :
    rp (fun i => (Fsc i)⁻¹ * A i) b (fun i => (Fsc i)ᵀ *ᵥ x i) = rp A b x ∧
    (∀ i, Rd (fun i => (Fsc i)⁻¹ * A i) (fun i => (Fsc i)⁻¹ *ᵥ c i) (fun i => (Fsc i)⁻¹ *ᵥ z i) y i
        = (Fsc i)⁻¹ *ᵥ Rd A c z y i) ∧
    (∀ i, gammaSq ((Fsc i)⁻¹ *ᵥ z i) = gammaSq (z i)) ∧
    (∀ i, Mblock (GHKM ((Fsc i)⁻¹ *ᵥ z i)) ((Fsc i)⁻¹ * A i) ((Fsc i)ᵀ *ᵥ x i) ((Fsc i)⁻¹ *ᵥ z i)
        = Mblock (GHKM (z i)) (A i) (x i) (z i)) ∧
    schurM .hkm (fun i => (Fsc i)⁻¹ * A i) (fun i => (Fsc i)ᵀ *ᵥ x i) (fun i => (Fsc i)⁻¹ *ᵥ z i)
      = schurM .hkm A x z ∧
    schurH .hkm (fun i => (Fsc i)⁻¹ * A i) b (fun i => (Fsc i)⁻¹ *ᵥ c i)
        (fun i => (Fsc i)ᵀ *ᵥ x i) y (fun i => (Fsc i)⁻¹ *ᵥ z i) σ
      = schurH .hkm A b c x y z σ := by sorry

end SDPT3.ScaleInv
