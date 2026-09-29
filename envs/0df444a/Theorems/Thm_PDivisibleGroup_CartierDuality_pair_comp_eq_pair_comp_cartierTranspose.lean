-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_pair_comp_eq_pair_comp_cartierTranspose
-- name    : PDivisibleGroup.CartierDuality.pair_comp_eq_pair_comp_cartierTranspose
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/eafd8ae2-72af-5f2d-ade9-ee3fbd2fecad
-- title:
--   Cartier transpose is adjoint for the Cartier pairing on points
-- statement:
--   Fix a commutative ring $R$, natural numbers $p$ and $h$, and two $p$-divisible groups $G, G'$ over $R$ of height data $(p,h)$, that is, systems of finite free cocommutative Hopf $R$-algebras $G.\mathrm{level}\,v$ with surjective bialgebra transition maps, prescribed ranks $p^{vh}$ and transition kernels the $p^v$-torsion ideals. Let $D$ be a Cartier duality datum between them: bialgebra equivalences $D.\mathrm{equiv}\,v : G'.\mathrm{level}\,v \simeq \mathrm{CartierDual}\,R\,(G.\mathrm{level}\,v)$ for all $v$, compatible with the transition maps through multiplication by $p$. Fix a level $v$, a bialgebra endomorphism $u$ of $G.\mathrm{level}\,v$, a commutative $R$-algebra $L$, and points $f \in G.\mathrm{Point}\,L\,v$, $\psi \in G'.\mathrm{Point}\,L\,v$, i.e. $R$-algebra maps into $L$ from $G.\mathrm{level}\,v$ and $G'.\mathrm{level}\,v$ respectively (recorded in the convolution monoid). The assertion is that the pairing $D.\mathrm{pair}\,L\,v$, defined on points by $\sum_i f(b_i)\,\psi\big((D.\mathrm{toDualEquiv}\,v)^{-1}(b_i^{\vee})\big)$ for a chosen basis $b$ of the free $R$-module $G.\mathrm{level}\,v$, satisfies $\langle f \circ u, \psi\rangle = \langle f, \psi \circ u'\rangle$, where the Cartier transpose $u'$ is the $R$-algebra endomorphism of $G'.\mathrm{level}\,v$ given by $D.\mathrm{equiv}\,v$ followed by $\mathrm{CartierDual.map}\,u$ (precomposition with $u$ on dual vectors) followed by $(D.\mathrm{equiv}\,v)^{-1}$.
--
--   This is the adjointness of an endomorphism of a finite locally free commutative group scheme and its Cartier dual endomorphism with respect to the Cartier pairing $G_v \times G_v^{\vee} \to \mathbb{G}_m$ evaluated on $L$-valued points. It is used to transport an endomorphism across the pairing of Tate modules, in the comparison of an endomorphism of the Tate module of $G$ with a scalar ([`PDivisibleGroup.CartierDuality.moduleEnd_tateModuleRep_eq_smul_of_forall_point_comp_cartierTranspose_valuation_sub_pow_lt_one`](thm.html#PDivisibleGroup.CartierDuality.moduleEnd_tateModuleRep_eq_smul_of_forall_point_comp_cartierTranspose_valuation_sub_pow_lt_one)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_pair_comp_eq_pair_comp_cartierTranspose.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CartierDualMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.CartierDuality.pair_comp_eq_pair_comp_cartierTranspose
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (v : ℕ) (u : G.level v →ₐc[R] G.level v)
    (L : Type) [CommRing L] [Algebra R L]
    (f : G.Point L v) (ψ : G'.Point L v) :
    D.pair L v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp (u : G.level v →ₐ[R] G.level v))) ψ =
      D.pair L v f (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom ψ).comp
        (((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v).comp
          ((CartierDual.map u).comp (D.equiv v : G'.level v →ₐc[R] CartierDual R (G.level v))) :
            G'.level v →ₐ[R] G'.level v))) := by sorry
