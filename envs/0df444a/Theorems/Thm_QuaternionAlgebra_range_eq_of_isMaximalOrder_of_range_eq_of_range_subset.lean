-- Prove2me | Theorems.Thm_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset
-- name    : QuaternionAlgebra.range_eq_of_isMaximalOrder_of_range_eq_of_range_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/2698179f-878c-55b8-a2c1-cb79c7504ea8
-- title:
--   Embeddings of a maximal order into a maximal order are onto
-- statement:
--   Let $a,b$ be rational numbers and $\mathbb{H}[\mathbb{Q},a,b]$ the associated quaternion algebra over $\mathbb{Q}$. Let $E$ be a ring and let $\theta,\theta' \colon E \to \mathbb{H}[\mathbb{Q},a,b]$ be injective ring homomorphisms. Let $\Lambda',\Lambda$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$, each assumed to be a maximal order in the following sense: the submodule contains $1$, is closed under multiplication, its $\mathbb{Q}$-span is all of $\mathbb{H}[\mathbb{Q},a,b]$, it is finitely generated as a $\mathbb{Z}$-module, and every $\mathbb{Z}$-submodule with these four properties that contains it is equal to it. Assume moreover that the image of $\theta$ is exactly the set underlying $\Lambda'$, and that the image of $\theta'$ is contained in the set underlying $\Lambda$. The conclusion is that the image of $\theta'$ is equal to the set underlying $\Lambda$, i.e. the inclusion $\theta'(E) \subseteq \Lambda$ is an equality.
--
--   This is the rigidity statement that a ring abstractly isomorphic to a maximal order of a rational quaternion algebra cannot embed properly into a maximal order: any such embedding with image inside an order $\Lambda$ already fills out $\Lambda$. It is used in the Čerednik–Drinfel'd part of the development, in [`CerednikDrinfeld.exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq`](thm.html#CerednikDrinfeld.exists_ringHom_range_eq_conjByFiniteIdele_forall_apply_eq_mul_of_image_kernelIdealSet_eq), to identify images of orders under constructed ring homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_range_eq_of_isMaximalOrder_of_range_eq_of_range_subset.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Quaternion

theorem QuaternionAlgebra.range_eq_of_isMaximalOrder_of_range_eq_of_range_subset
    {a b : ℚ} {E : Type*} [Ring E] (θ θ' : E →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθ' : Function.Injective θ')
    {Λ' Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ' : QuaternionAlgebra.IsMaximalOrder Λ') (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (hrange : Set.range θ = (Λ' : Set ℍ[ℚ, a, b])) (hsub : Set.range θ' ⊆ (Λ : Set ℍ[ℚ, a, b])) :
    Set.range θ' = (Λ : Set ℍ[ℚ, a, b]) := by sorry
