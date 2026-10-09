-- Prove2me | Theorems.Thm_SphereSOS_DPS_eq_39
-- name    : SphereSOS.DPS.eq_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:41.75427+00:00
-- url     : https://prove2.me/theorems/b5a4938a-233f-4fa7-93c9-693722ad0e4e
-- title:
--   (39), p. 17 — (x ⊗ y^{⊗ℓ})†(Y − (I ⊗ Π_ℓ)Y(I ⊗ Π_ℓ))(x ⊗ y^{⊗ℓ}) = 0
-- statement:
--   Let $\ell\ge1$, let $\Pi_\ell$ be the orthogonal projector onto the symmetric subspace of $\mathcal H_B^{\otimes\ell}$, $\mathcal H_B\simeq\mathbb C^{d_B}$, and let $Y$ be a Hermitian operator on $\mathcal H_A\otimes\mathcal H_B^{\otimes\ell}$. Then
--   $$\big(x\otimes y^{\otimes\ell}\big)^\dagger\big(Y-(I\otimes\Pi_\ell)Y(I\otimes\Pi_\ell)\big)\big(x\otimes y^{\otimes\ell}\big)=0\qquad\forall x\in\mathcal H_A,\ y\in\mathcal H_B.$$
--
--   In the proof of Theorem 12 (ii) this removes the dual variable of the symmetry constraint (21) when the dual description of $\mathcal{DPS}_\ell^*$ is evaluated on product vectors $x\otimes y^{\otimes\ell}$.
--
--   **Formalization Note** The level is $\ell=m+1$; $\Pi_\ell=\frac1{\ell!}\sum_{\sigma\in\mathfrak S_\ell}P_\sigma$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 17, (39)

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

namespace SphereSOS.DPS

open scoped ComplexOrder

/-- (39) (p. 17), with ℓ = m + 1: for Y ∈ Herm,
(x ⊗ y^{⊗ℓ})† (Y − (I ⊗ Π_ℓ) Y (I ⊗ Π_ℓ)) (x ⊗ y^{⊗ℓ}) = 0 for all x, y. -/
theorem eq_39 {dA dB m : ℕ} (Y : Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ) (hY : Y.IsHermitian)
    (x : Fin dA → ℂ) (y : Fin dB → ℂ) :
    qf (tensVec 0 x y) (Y - symProj (m + 1) * Y * symProj (m + 1)) = 0 := by sorry

end SphereSOS.DPS
