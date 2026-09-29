-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced
-- name    : PDivisibleGroup.CartierDuality.pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/59830951-bda0-5a2f-8f2b-72a7e17a59b7
-- title:
--   Formal points pair trivially at an ordinary level
-- statement:
--   Fix a prime $p$, a discrete valuation domain $O$ equipped with algebra maps to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` and to $\mathbb{Z}/p$, and a valuation subring $P$ of $\overline{\mathbb{Q}}$ such that every element of $O$ maps into $P$ (hypothesis `hOP`) and such that, for $x \in O$, the image of $x$ in $\mathbb{Z}/p$ vanishes precisely when the valuation of its image in $\overline{\mathbb{Q}}$ is $< 1$ (hypothesis `hres`). Let $H, H'$ be $p$-divisible groups over $O$ of height $h$ — families of commutative, cocommutative $O$-Hopf algebras `level v`, finite and free of rank $p^{vh}$, with surjective bialgebra transitions whose kernels are the $p^v$-torsion ideals — and let $D$ be a Cartier duality datum between them: bialgebra isomorphisms $H'.\mathrm{level}\,v \cong \mathrm{CartierDual}\,O\,(H.\mathrm{level}\,v)$ compatible with the transitions and multiplication by $p$. Fix a level $v$ and assume the ordinarity hypothesis `hord`: there are a finite free $\mathbb{Z}/p$-Hopf algebra $M$ and a $\mathbb{Z}/p$-Hopf algebra $E$ with a bijective bialgebra map $\mathbb{Z}/p \otimes_O H.\mathrm{level}\,v \to M \otimes_{\mathbb{Z}/p} E$ such that $E$ and the Cartier dual of $M$ are reduced. Then for points $f$ of $H$ and $\psi$ of $H'$ at level $v$ over $\overline{\mathbb{Q}}$ (i.e. $O$-algebra maps from the respective level-$v$ Hopf algebras, with convolution group structure) whose values differ from those of the counit by elements of valuation $< 1$, the pairing $D.\mathrm{pair}$ at level $v$ — the sum over a chosen $O$-basis $(e_i)$ of $H.\mathrm{level}\,v$ of $f(e_i)\,\psi(\lambda_i)$, where $\lambda_i$ corresponds to the $i$-th coordinate functional under the duality — equals $1$.
--
--   This is the orthogonality of the formal (identity-component) points to the formal points of the dual under the Cartier pairing, at a level whose special fibre is ordinary, in the sense that it splits as a tensor product of a Hopf algebra of multiplicative type and a reduced one. It is used in the determination of the inertia action on the Tate module of an ordinary $p$-divisible group, through [`PDivisibleGroup.exists_rep_pow_sub_smul_eq_cyclotomicCharacter_smul_of_reduction_pow_eq_frobenius_conv_verschiebung`](thm.html#PDivisibleGroup.exists_rep_pow_sub_smul_eq_cyclotomicCharacter_smul_of_reduction_pow_eq_frobenius_conv_verschiebung).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PDivisibleGroup_CartierDuality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.CartierDuality.pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ} (H H' : PDivisibleGroup O p h) (D : H.CartierDuality H')
    (v : ℕ)

    (hord : ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : ZMod p ⊗[O] H.level v →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M))
    (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v)
    (hf : ∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
      algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)
    (hψ : ∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
      algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    D.pair (AlgebraicClosure ℚ) v f ψ = 1 := by sorry
