-- Prove2me | Theorems.Thm_PDivisibleGroup_CartierDuality_pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one
-- name    : PDivisibleGroup.CartierDuality.pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/96df6471-5395-5235-86b5-6a3b2ee064a8
-- title:
--   Cartier pairing equals 1 on étale-dual factors and formal points
-- statement:
--   Let $p$ be a prime and let $O$ be a commutative ring equipped with an algebra map to $\overline{\mathbb{Q}}$, let $P$ be a valuation subring of $\overline{\mathbb{Q}}$, and assume every element of $O$ maps into $P$. Let $H,H'$ be $p$-divisible groups over $O$ of height $h$ in the sense of [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199) (levels `level v` that are finite free cocommutative Hopf $O$-algebras of rank $p^{vh}$, with surjective bialgebra transition maps whose kernels are the $p^v$-torsion ideals), and let $D$ be a Cartier duality datum between them: bialgebra isomorphisms $H'.\mathrm{level}\,v \cong \mathrm{CartierDual}\,O\,(H.\mathrm{level}\,v)$, the $O$-linear dual, compatible with the transition maps and multiplication by $p$. Fix $v \in \mathbb{N}$. Let $M_t$ be a commutative ring that is a cocommutative Hopf $O$-algebra, finite and free as an $O$-module, whose Cartier dual $\mathrm{CartierDual}\,O\,M_t$ is étale over $O$, and let $\pi : H.\mathrm{level}\,v \to M_t$ be a morphism of $O$-bialgebras. Let $f$ be a point of $H$ at level $v$ with values in $\overline{\mathbb{Q}}$ (an $O$-algebra map $H.\mathrm{level}\,v \to \overline{\mathbb{Q}}$, the points being a group under convolution) and $g : M_t \to \overline{\mathbb{Q}}$ an $O$-algebra map, and suppose the algebra map underlying $f$ is $\pi$ followed by $g$. Let $\psi$ be a point of $H'$ at level $v$ over $\overline{\mathbb{Q}}$ such that for every $a \in H'.\mathrm{level}\,v$ the $P$-valuation of $\psi(a) - \varepsilon(a)$ is $<1$, where $\varepsilon$ is the counit and its value is taken in $\overline{\mathbb{Q}}$ via $O$. Then the Cartier pairing $\sum_i f(e_i)\,\psi\bigl((D.\mathrm{toDualEquiv}\,v)^{-1}(e_i^{*})\bigr)$, computed over a chosen $O$-basis $(e_i)$ of $H.\mathrm{level}\,v$ with dual coordinate functionals $e_i^{*}$, equals $1$.
--
--   This is the orthogonality statement that a point factoring through a quotient of multiplicative type pairs trivially against a point of the dual group which is congruent to the identity at $P$, the group-scheme form of the assertion that a homomorphism from a connected group to an étale group over a henselian base is trivial; no ordinarity hypothesis enters, the henselianity of the absolutely integrally closed valuation ring $P$ doing the work. It is used in the computation of the action of Frobenius and the diamond operators on the Tate module of a modular curve in the ordinary case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_CartierDuality_pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one.lean

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

theorem PDivisibleGroup.CartierDuality.pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} (H H' : PDivisibleGroup O p h) (D : H.CartierDuality H')
    (v : ℕ)

    (Mt : Type) [CommRing Mt] [HopfAlgebra O Mt] [Coalgebra.IsCocomm O Mt] [Module.Free O Mt] [Module.Finite O Mt]
    [Algebra.Etale O (CartierDual O Mt)]
    (π : H.level v →ₐc[O] Mt)
    (f : H.Point (AlgebraicClosure ℚ) v) (g : Mt →ₐ[O] AlgebraicClosure ℚ)
    (hfg : PDivisibleGroup.Point.toAlgHom f = g.comp (π : H.level v →ₐ[O] Mt))

    (ψ : H'.Point (AlgebraicClosure ℚ) v)
    (hψ : ∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
      algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    D.pair (AlgebraicClosure ℚ) v f ψ = 1 := by sorry
