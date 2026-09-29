-- Prove2me | Theorems.Thm_WLight_exists_mdifferentiable_div_of_monicRel
-- name    : WLight.exists_mdifferentiable_div_of_monicRel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/9663f68b-21af-5bc5-ae59-24171b015314
-- title:
--   Holomorphic divisibility from a cleared monic relation on H
-- statement:
--   Let $a, b \colon \mathbb{H} \to \mathbb{C}$ be functions on the upper half-plane that are differentiable in the manifold sense for the model $\mathcal{I}(\mathbb{C})$ on source and target, i.e. holomorphic as functions on the complex manifold $\mathbb{H}$, let $d$ be a natural number, and let $c \colon \mathbb{N} \to (\mathbb{H} \to \mathbb{C})$ be a family of functions such that $c_k$ is holomorphic in the same sense for every $k < d$ (no condition is imposed on $c_k$ for $k \ge d$). Assume $b$ is not the zero function, and assume the identity $$a^d + \sum_{k < d} c_k \, b^{\,d-k}\, a^k = 0$$ holds in the ring of $\mathbb{C}$-valued functions on $\mathbb{H}$ with pointwise operations, that is, pointwise on all of $\mathbb{H}$ (the exponent $d-k$ being truncated subtraction of naturals, harmless since $k < d$). Then there exists a holomorphic $F \colon \mathbb{H} \to \mathbb{C}$ with $F \cdot b = a$ as functions on $\mathbb{H}$, the product again being pointwise; thus the equality holds at every point, not merely off the zero set of $b$.
--
--   This is the upper-half-plane form of the classical clearing argument: a monic algebraic relation for the quotient $a/b$, multiplied through by $b^d$, forces $b$ to divide $a$ in the ring of holomorphic functions. It is obtained from [`WLight.exists_analyticOnNhd_div_of_monicRel`](thm.html#WLight.exists_analyticOnNhd_div_of_monicRel) on the connected open subset of $\mathbb{C}$ underlying $\mathbb{H}$, and is used to reconstruct genuine holomorphic functions, and hence cusp forms, from algebraic data, as in [`CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff`](thm.html#CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff) and the statements on $q$-expansion coefficients of bases of cusp forms for $\Gamma_1(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_exists_mdifferentiable_div_of_monicRel.lean

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.exists_mdifferentiable_div_of_monicRel {a b : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}
    (hahol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a) (hbhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b)
    (hb0 : b ≠ 0) (hc : ∀ k < d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c k))
    (hrel : a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0) :
    ∃ F : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ F * b = a := by sorry
