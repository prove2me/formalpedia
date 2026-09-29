-- Prove2me | Theorems.Thm_QuaternionAlgebra_projGenLinGroup_mk_unitsMap_eq_one_iff
-- name    : QuaternionAlgebra.projGenLinGroup_mk_unitsMap_eq_one_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/dcfbb8ea-a827-59ca-863f-eed500fb5893
-- title:
--   Triviality criterion for the projective image of a quaternion unit
-- statement:
--   Let $a,b$ be nonzero rationals, so that $\mathbb{H}[\mathbb{Q},a,b]$ is the quaternion algebra over $\mathbb{Q}$ with $i^2=a$, $j^2=b$, and let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure. Suppose given an injective $\mathbb{Q}$-algebra homomorphism $\iota\colon \mathbb{H}[\mathbb{Q},a,b]\to M_2(L)$ and a group homomorphism $\rho$ from the unit group $\mathbb{H}[\mathbb{Q},a,b]^\times$ to $\mathrm{PGL}(2,L)$ (Mathlib's `Matrix.ProjGenLinGroup`, i.e. $\mathrm{GL}_2(L)$ modulo its centre) which is assumed to be the composite of $\iota$ with the projection: for every unit $x$, $\rho(x)$ is the class of the image of $x$ under the unit-group map induced by $\iota$. The conclusion is that for every unit $x$ of $\mathbb{H}[\mathbb{Q},a,b]$ one has $\rho(x)=1$ if and only if there exists a nonzero rational $c$ with $x=c\cdot 1$, i.e. the underlying element of $x$ is the image of $c$ under the structure map $\mathbb{Q}\to\mathbb{H}[\mathbb{Q},a,b]$. Thus the kernel of $\rho$ consists exactly of the rational scalars.
--
--   This is the faithfulness statement for the projective representation of a quaternion unit group: the kernel of $\mathbb{H}^\times\to\mathrm{PGL}_2(L)$ attached to an embedding $\iota$ is the centre $\mathbb{Q}^\times$. It is used in the Čerednik–Drinfeld part of the development, where the projective action of a quaternion unit group on a tree or $p$-adic symmetric space must be known to be trivial only on rational scalars.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_projGenLinGroup_mk_unitsMap_eq_one_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups

theorem QuaternionAlgebra.projGenLinGroup_mk_unitsMap_eq_one_iff
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (L : Type) [Field L] [Algebra ℚ L]
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) L) (hι : Function.Injective ι)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, L))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) L) x)) :
    ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = 1 ↔ ∃ c : ℚ, c ≠ 0 ∧ (x : ℍ[ℚ, a, b]) = algebraMap ℚ ℍ[ℚ, a, b] c := by sorry
