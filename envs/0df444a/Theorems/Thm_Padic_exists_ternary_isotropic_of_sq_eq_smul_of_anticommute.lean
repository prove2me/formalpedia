-- Prove2me | Theorems.Thm_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute
-- name    : Padic.exists_ternary_isotropic_of_sq_eq_smul_of_anticommute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/c043e75d-2a51-5ddd-a92b-b30e9a844409
-- title:
--   Anticommuting endomorphisms make z²=ux²+vy² isotropic over ℚ_ℓ
-- statement:
--   Let $\ell$ be a prime and let $A$ be an additive commutative group, regarded as a $\mathbb{Z}$-module, such that for every natural number $n$ the $\ell^n$-torsion subgroup of $A$ — the submodule of elements annihilated by the integer $\ell^n$, written `Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ)` — admits an isomorphism of additive groups with $\mathbb{Z}/\ell^n \times \mathbb{Z}/\ell^n$ (the hypothesis asserts only that the type of such isomorphisms is nonempty, for each $n$). Let $u, v$ be integers and let $i, j \colon A \to A$ be additive group endomorphisms satisfying, pointwise on $A$, the identities $i(i(a)) = u \cdot a$, $j(j(a)) = v \cdot a$ and $i(j(a)) = -\,j(i(a))$, where $\cdot$ denotes the $\mathbb{Z}$-action on $A$. The conclusion is that the ternary quadratic form $z^2 - ux^2 - vy^2$ is isotropic over the field $\mathbb{Q}_\ell$ of $\ell$-adic numbers: there are $z, x, y \in \mathbb{Q}_\ell$ for which it is not the case that $z = 0$, $x = 0$ and $y = 0$ all hold, and such that $z^2 - ux^2 - vy^2 = 0$, the images of $u$ and $v$ in $\mathbb{Q}_\ell$ being understood.
--
--   This is the abstract group-theoretic core of the classical fact that a quaternion algebra $\left(\frac{u,v}{\mathbb{Q}}\right)$ occurring inside the endomorphism algebra of an elliptic curve is split at every prime $\ell$ different from the characteristic, the usual argument being the faithful action on the rank-two $\ell$-adic Tate module; here the curve is replaced by a group all of whose $\ell^n$-torsion is $(\mathbb{Z}/\ell^n)^2$. It is used in the study of endomorphisms of Weierstrass curves, via [`WeierstrassCurve.exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero`](thm.html#WeierstrassCurve.exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Padic.exists_ternary_isotropic_of_sq_eq_smul_of_anticommute {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (hA : ∀ n : ℕ, Nonempty (ZMod (ℓ ^ n) × ZMod (ℓ ^ n) ≃+ Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ))) (u v : ℤ) (i j : A →+ A) (hi : ∀ a, i (i a) = u • a) (hj : ∀ a, j (j a) = v • a) (hij : ∀ a, i (j a) = -(j (i a))) : ∃ z x y : ℚ_[ℓ], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - (u : ℚ_[ℓ]) * x ^ 2 - (v : ℚ_[ℓ]) * y ^ 2 = 0 := by sorry
