-- Prove2me | Theorems.Thm_QuaternionAlgebra_isOrder_toIntSubmodule_range_comp_includeRight
-- name    : QuaternionAlgebra.isOrder_toIntSubmodule_range_comp_includeRight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/43c20078-bc56-5286-828e-51e0e5372cc4
-- title:
--   Image of a finite free ℤ-algebra is a quaternion order
-- statement:
--   Let $O$ be a ring that is free and finite as a $\mathbb{Z}$-module, let $a,b \in \mathbb{Q}$, and let $e \colon \mathbb{Q} \otimes_{\mathbb{Z}} O \to \mathbb{H}[\mathbb{Q},a,b]$ be an isomorphism of $\mathbb{Q}$-algebras onto the quaternion algebra with parameters $a,b$ over $\mathbb{Q}$. Consider the ring homomorphism $\theta \colon O \to \mathbb{H}[\mathbb{Q},a,b]$ obtained by composing the right inclusion $o \mapsto 1 \otimes o$ of $O$ into $\mathbb{Q} \otimes_{\mathbb{Z}} O$ with $e$. The assertion is twofold: first, $\theta$ is injective; second, the range of $\theta$, regarded as a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ (via its underlying additive subgroup), satisfies the predicate [`QuaternionAlgebra.IsOrder`](def/QuaternionAlgebra_Order.html#L11), i.e. all four of: $1 \in \Lambda$; $xy \in \Lambda$ whenever $x,y \in \Lambda$; the $\mathbb{Q}$-span of $\Lambda$ inside $\mathbb{H}[\mathbb{Q},a,b]$ is the whole algebra; and $\Lambda$ is finitely generated as a $\mathbb{Z}$-module.
--
--   This records that a $\mathbb{Z}$-algebra which is finite free as a $\mathbb{Z}$-module and whose rationalisation is a given quaternion algebra embeds into that quaternion algebra with image an order in the sense used throughout the project. It serves as the passage from an abstract finite free $\mathbb{Z}$-algebra to a concrete lattice, and is used in the construction of a maximal order in a definite quaternion algebra ramified exactly at a prescribed set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_isOrder_toIntSubmodule_range_comp_includeRight.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isOrder_toIntSubmodule_range_comp_includeRight
    (O : Type*) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O]
    {a b : ℚ} (e : ℚ ⊗[ℤ] O ≃ₐ[ℚ] ℍ[ℚ, a, b]) :
    Function.Injective
        ((e : ℚ ⊗[ℤ] O →+* ℍ[ℚ, a, b]).comp
          (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O).toRingHom) ∧
      QuaternionAlgebra.IsOrder (AddSubgroup.toIntSubmodule
        ((e : ℚ ⊗[ℤ] O →+* ℍ[ℚ, a, b]).comp
          (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] ℚ ⊗[ℤ] O).toRingHom).range.toAddSubgroup) := by sorry
