-- Prove2me | Theorems.Thm_PDivisibleGroup_Tower_map_hopfKer_transitionLE_succ_eq
-- name    : PDivisibleGroup.Tower.map_hopfKer_transitionLE_succ_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/8e8b1417-6853-5a72-a8e9-f13a69c4818d
-- title:
--   Transitions map Hopf kernels onto Hopf kernels in a tower
-- statement:
--   Let $R$ be a commutative local ring, let $i_0$ be a natural number, and let $B$ be a family of types $B_w$ ($w \in \mathbb{N}$), each a commutative ring carrying a Hopf $R$-algebra structure whose comultiplication is cocommutative, and finite and free as an $R$-module. Let $t_w \colon B_{w+1} \to B_w$ be $R$-bialgebra homomorphisms, each surjective, and for $v \in \mathbb{N}$ let $T_v = \mathtt{transitionLE}\ t\ i_0\ v \colon B_{i_0+v} \to B_{i_0}$ be the composite $t_{i_0} \circ \dots \circ t_{i_0+v-1}$ defined by $T_0 = \mathrm{id}$ and $T_{u+1} = T_u \circ t_{i_0+u}$. For a bialgebra map $\pi \colon A \to C$ write $\mathrm{hopfKer}(\pi)$ for the $R$-subalgebra of $A$ on which the two algebra maps $A \to A \otimes_R C$ given by comultiplication followed by $\mathrm{id} \otimes \pi$, and by $a \mapsto a \otimes 1$, agree. Assume that $\mathrm{hopfKer}(T_v)$ is a free $R$-module for every $v$. Then for every $v$ the image of the subalgebra $\mathrm{hopfKer}(T_{v+1}) \subseteq B_{i_0+v+1}$ under the algebra map underlying $t_{i_0+v}$ is exactly $\mathrm{hopfKer}(T_v) \subseteq B_{i_0+v}$.
--
--   In the Hopf-algebra language for $p$-divisible groups, $\mathrm{hopfKer}(T_v)$ is the coordinate algebra of the quotient $E_{i_0+v}/E_{i_0}$, and the statement says that the transition $t_{i_0+v}$ restricts to a surjection of these coinvariant algebras, i.e. that the induced maps of quotients are closed immersions. It supplies the surjectivity axiom for the tower $\Gamma^{(i_0)} = (E_{i_0+v}/E_{i_0})_v$ and is used by [`PDivisibleGroup.Tower.exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer`](thm.html#PDivisibleGroup.Tower.exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_Tower_map_hopfKer_transitionLE_succ_eq.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.Tower.map_hopfKer_transitionLE_succ_eq
    {R : Type} [CommRing R] [IsLocalRing R] (i₀ : ℕ)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (t : ∀ w, B (w + 1) →ₐc[R] B w) (ht : ∀ w, Function.Surjective (t w))
    (hfree : ∀ v, Module.Free R ↥(HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))) (v : ℕ) :
    (HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1))).map
        (t (i₀ + v) : B (i₀ + v + 1) →ₐ[R] B (i₀ + v)) =
      HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v) := by sorry
