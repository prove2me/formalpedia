-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two
-- name    : QuaternionAlgebra.IsOrder.exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/aeb64a16-1156-5ccd-b09f-f65d62c286f1
-- title:
--   Standard coordinates for two-dimensional complex Λ-modules
-- statement:
--   Let $q,q'$ be primes and $a,b \in \mathbb{Q}$, and suppose the quaternion algebra $B = \mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible precisely when $q \in v$ or $q' \in v$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is an order in the sense of `IsOrder`: it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, and is finitely generated over $\mathbb{Z}$. Let $\iota : B \to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra homomorphism, let $V$ be a complex vector space with $\dim_{\mathbb{C}} V = 2$, and let $\rho$ assign to each element of $\Lambda$ a $\mathbb{C}$-linear endomorphism of $V$ in such a way that $\rho$ is additive, $\rho(1) = \mathrm{id}$, and $\rho(xy) = \rho(x) \circ \rho(y)$ for $x,y \in \Lambda$. Then there is a $\mathbb{C}$-linear isomorphism $P : V \to \mathbb{C}^2$ with $P(\rho(x)v) = \iota(x) \cdot P(v)$ for all $x \in \Lambda$ and $v \in V$, the matrix $\iota(x)$ being read entrywise in $\mathbb{C}$ and acting by matrix–vector multiplication.
--
--   This is the 'standard coordinates' statement that, up to a change of basis, the only unital action of an order $\Lambda$ in an indefinite quaternion algebra on a two-dimensional complex vector space is the one obtained from a splitting $\iota$ at the archimedean place; rigidity of this kind comes from the Skolem–Noether theorem. It is used in the construction of the quaternionic uniformisation, in [`CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic`](thm.html#CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic), to normalise the $\Lambda$-action on the tangent space of an abelian surface with quaternionic multiplication.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsOrder.exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (V : Type) [AddCommGroup V] [Module ℂ V] (hV : Module.finrank ℂ V = 2)
    (ρ : ↥Λ → (V →ₗ[ℂ] V))
    (hρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id)
    (hρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (hρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y) :
    ∃ P : V ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ (x : ↥Λ) (v : V),
      P (ρ x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (P v) := by sorry
