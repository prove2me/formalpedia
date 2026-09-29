-- Prove2me | Theorems.Thm_PDivisibleGroup_Tower_forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp
-- name    : PDivisibleGroup.Tower.forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/fc3d53ec-ade2-5a60-a042-52466025cb47
-- title:
--   Reduced Cartier duals propagate up a p-divisible tower over 𝔽ₚ
-- statement:
--   Fix a prime $p$ and a natural number $h$, and let $L : \mathbb{N} \to \mathrm{Type}$ assign to each $v$ a commutative ring $L_v$ carrying a cocommutative Hopf algebra structure over $\mathbb{Z}/p$ that is finite as a $\mathbb{Z}/p$-module. Suppose given transition maps $t_v : L_{v+1} \to L_v$ of $\mathbb{Z}/p$-bialgebras, each surjective, such that $\operatorname{rank}_{\mathbb{Z}/p} L_v = p^{vh}$ for all $v$, and such that for every $v$ the kernel of $t_v$ is the $p^v$-torsion ideal of $L_{v+1}$, that is, the image of the augmentation ideal $\ker(\varepsilon_{L_{v+1}})$ under the algebra endomorphism $[p^v]$ of $L_{v+1}$ obtained as the $p^v$-fold convolution power of the identity. These are exactly the data and axioms of a $p$-divisible tower of height $h$ over $\mathbb{Z}/p$ (freeness over the field $\mathbb{Z}/p$ being automatic). The hypothesis is that the Cartier dual of $L_1$, namely the $\mathbb{Z}/p$-linear dual $\operatorname{Hom}_{\mathbb{Z}/p}(L_1, \mathbb{Z}/p)$ with its ring structure, is reduced. The conclusion is that for every $v \in \mathbb{N}$ the Cartier dual of $L_v$ is reduced.
--
--   This is the statement that a $p$-divisible group over $\mathbb{F}_p$ whose first level is of multiplicative type (reduced Cartier dual) has all levels of multiplicative type, the reducedness being propagated along the extensions $0 \to G_v \to G_{v+1} \to G_1 \to 0$ of the tower. It is used in the analysis of the $p$-divisible group attached to the Néron model of a modular Jacobian at $p$, and in the corresponding statement for towers over more general base rings after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Tower_forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe v

theorem PDivisibleGroup.Tower.forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra (ZMod p) (L v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (L v)] [∀ v, Module.Finite (ZMod p) (L v)]
    (t : ∀ v, L (v + 1) →ₐc[ZMod p] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank (ZMod p) (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (L (v + 1)) (p ^ v))
    (hred₁ : IsReduced (CartierDual (ZMod p) (L 1))) :
    ∀ v : ℕ, IsReduced (CartierDual (ZMod p) (L v)) := by sorry
