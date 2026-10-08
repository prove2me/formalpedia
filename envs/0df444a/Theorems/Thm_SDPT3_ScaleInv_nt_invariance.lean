-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_nt_invariance
-- name    : SDPT3.ScaleInv.nt_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:09.577453+00:00
-- url     : https://prove2.me/theorems/e1310955-2b7f-487f-8773-d3a72d4f074c
-- title:
--   Proof of Proposition 1, p. 12 — NT step: γ(x̂) = γ(x), ω̂ = ω, ξ̂ = F⁻¹ξ, t̂ = F⁻¹t, and M_i is invariant
-- statement:
--   Let $F$ be a real $q\times q$ matrix with $F^\top \bar J F = \bar J$ and $F_{00} > 0$, let $x, z \in \mathbb R^q$ lie in the interior of the second-order cone, let $A_i \in \mathbb R^{q\times m}$, and set $\hat x = F^\top x$, $\hat z = F^{-1} z$, $\hat A_i = F^{-1} A_i$. With $\omega$, $\xi$, $t$ of (20)–(21),
--   1. $\gamma(\hat x) = \gamma(x)$;
--   2. $\hat\omega = \omega$, i.e. $\omega$ is unchanged by the scaling;
--   3. $\hat\xi = F^{-1}\xi$;
--   4. $\hat t = F^{-1} t$;
--   5. the NT block of the Schur complement matrix is unchanged: $\hat M_i = M_i$.
--
--   These are the invariances from which the proof concludes that the NT direction is scale-invariant.
--
--   **Formalization Note** As in the HKM step, the hypothesis is the printed identity $F^\top \bar J F = \bar J$ of (31) together with $F_{00} > 0$, i.e. the case $\lambda = 1$ of $\mathcal G_i$. For $\lambda F$ with $\lambda \ne 1$ one has instead $\hat\omega = \omega/\lambda$ and $\hat t = \lambda F^{-1} t$; the goal theorem covers all of $\mathcal G_i$.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 12, proof of Proposition 1 (NT part)

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem nt_invariance {k m : ℕ} (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hF : Fᵀ * Jbar k * F = Jbar k) (hF0 : 0 < F 0 0)
    (x z : Fin (k + 1) → ℝ) (hx : socInt x) (hz : socInt z)
    (Ai : Matrix (Fin (k + 1)) (Fin m) ℝ) :
    gam (Fᵀ *ᵥ x) = gam x ∧
    omegaNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z) = omegaNT x z ∧
    xiNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z) = F⁻¹ *ᵥ xiNT x z ∧
    tNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z) = F⁻¹ *ᵥ tNT x z ∧
    Mblock (GNT (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z)) (F⁻¹ * Ai) (Fᵀ *ᵥ x) (F⁻¹ *ᵥ z) = Mblock (GNT x z) Ai x z := by sorry

end SDPT3.ScaleInv
