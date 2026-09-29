-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_algHom_matrix_injective
-- name    : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_algHom_matrix_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/62c51c4a-ad94-57d5-9cc0-97613f16459f
-- title:
--   Real splitting: indefinite rational quaternion algebra embeds in M₂(ℝ)
-- statement:
--   Let $q$ and $q'$ be natural numbers, each assumed prime as a typeclass hypothesis, and let $a,b\in\mathbb{Q}$. Write $B=\mathbb{H}[\mathbb{Q},a,b]$ for the rational quaternion algebra with $i^2=a$, $j^2=b$ and $ij=-ji$. Assume `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: (i) $a>0$ or $b>0$, and (ii) for every $v$ in the height one spectrum of the ring of integers of $\mathbb{Q}$, the algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ (the $v$-adic completion) has the property that each of its nonzero elements is a unit precisely when $q\in v$ or $q'\in v$, i.e. $v$ is the place of $q$ or of $q'$. The conclusion is the existence of a $\mathbb{Q}$-algebra homomorphism $\iota : B \to M_2(\mathbb{R})$, the algebra of $2\times 2$ real matrices, which is injective as a function. No further properties of $\iota$ (such as surjectivity after tensoring with $\mathbb{R}$, or compatibility with norm and trace) are asserted.
--
--   This is the real splitting of an indefinite rational quaternion algebra, providing the embedding $B\hookrightarrow M_2(\mathbb{R})$ used to realise units of an order as a Fuchsian group and hence to uniformise the associated Shimura curve. It is invoked in the construction of fake elliptic curves and in the statements about coarse moduli of quaternionic multiplication used in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_algHom_matrix_injective.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_algHom_matrix_injective
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q') :
    ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ, Function.Injective ι := by sorry
