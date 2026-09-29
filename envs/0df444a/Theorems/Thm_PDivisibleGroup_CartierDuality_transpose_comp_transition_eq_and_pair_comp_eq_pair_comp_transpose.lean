-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_transpose_comp_transition_eq_and_pair_comp_eq_pair_comp_transpose
-- name    : PDivisibleGroup.CartierDuality.transpose_comp_transition_eq_and_pair_comp_eq_pair_comp_transpose
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/c3aa101e-e546-55e2-b67b-b6fa05b97ba4
-- title:
--   Cartier duality of a morphism: transitions and pairing adjointness
-- statement:
--   Let $R$ be a commutative ring and $p,h,h'$ natural numbers. Let $G,G'$ be $p$-divisible groups over $R$ of height data $(p,h)$ together with Cartier duality data $D$, i.e. bialgebra equivalences $D_v\colon G'_v \xrightarrow{\sim} \mathrm{CartierDual}_R(G_v)$ compatible with the transition maps in the sense that $D_v(\mathrm{transition}_{G'}\,x)(\mathrm{transition}_G\,a) = D_{v+1}(x)(p\cdot_{\mathrm{Hopf}} a)$, where $p\cdot_{\mathrm{Hopf}}$ is the $p$-fold convolution power of the identity; let $\Gamma,\Gamma'$ with data $E$ be a second such pair, of height data $(p,h')$. Let $\varphi_v\colon G_v \to \Gamma_v$ be $R$-bialgebra maps for all $v$ with $\varphi_v \circ \mathrm{transition}_{G,v} = \mathrm{transition}_{\Gamma,v} \circ \varphi_{v+1}$. Put $\psi_v := D_v^{-1} \circ \mathrm{CartierDual.map}(\varphi_v) \circ E_v \colon \Gamma'_v \to G'_v$, the transpose of $\varphi_v$ carried through the duality data. Two assertions are made. First, $\psi_v \circ \mathrm{transition}_{\Gamma',v} = \mathrm{transition}_{G',v} \circ \psi_{v+1}$ as bialgebra maps $\Gamma'_{v+1} \to G'_v$, for every $v$. Second, for every commutative $R$-algebra $L$, every $v$, every $x \in \Gamma_v(L)$ and $y \in G'_v(L)$ (points being $R$-algebra maps from the level algebra to $L$, with the convolution group structure), $D$'s pairing applied to the point $x \circ \varphi_v$ and $y$ equals $E$'s pairing applied to $x$ and the point $y \circ \psi_v$, where the pairing of $D$ at level $v$ sends $f,\chi$ to $\sum_i f(b_i)\,\chi\bigl(D_v^{-1}(b_i^{\vee})\bigr)$ for the chosen basis $b$ of $G_v$ and its coordinate functionals.
--
--   This is the functoriality of Cartier duality for $p$-divisible groups in the levelwise form used in this development: the transpose of a morphism is again a morphism (it commutes with the transition maps), and it is adjoint to the original morphism for the Cartier pairings on $L$-valued points. It is used in the construction of a morphism of Tate modules from a morphism of $p$-divisible groups, in [`PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers`](thm.html#PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_transpose_comp_transition_eq_and_pair_comp_eq_pair_comp_transpose.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CartierDualMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.transpose_comp_transition_eq_and_pair_comp_eq_pair_comp_transpose
    {R : Type} [CommRing R] {p h h' : ℕ}
    {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    {Γ Γ' : PDivisibleGroup R p h'} (E : Γ.CartierDuality Γ')
    (φ : ∀ v : ℕ, G.level v →ₐc[R] Γ.level v)
    (hφ : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1))) :
    (∀ v : ℕ,
      (((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v).comp
          ((CartierDual.map (φ v)).comp (E.equiv v : Γ'.level v →ₐc[R] CartierDual R (Γ.level v)))).comp
        (Γ'.transition v) =
      (G'.transition v).comp
        (((D.equiv (v + 1)).symm : CartierDual R (G.level (v + 1)) →ₐc[R] G'.level (v + 1)).comp
          ((CartierDual.map (φ (v + 1))).comp (E.equiv (v + 1) : Γ'.level (v + 1) →ₐc[R] CartierDual R (Γ.level (v + 1)))))) ∧
    ∀ (L : Type) [CommRing L] [Algebra R L] (v : ℕ) (x : Γ.Point L v) (y : G'.Point L v),
      D.pair L v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : G.level v →ₐ[R] Γ.level v))) y =
        E.pair L v x (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp
          ((((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] G'.level v).comp
          ((CartierDual.map (φ v)).comp (E.equiv v : Γ'.level v →ₐc[R] CartierDual R (Γ.level v)))) :
            Γ'.level v →ₐ[R] G'.level v))) := by sorry
