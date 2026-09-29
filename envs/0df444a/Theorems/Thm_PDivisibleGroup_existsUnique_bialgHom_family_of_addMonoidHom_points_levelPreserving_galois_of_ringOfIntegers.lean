-- Prove2me | Theorems.Thm_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers
-- name    : PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/eace5b30-2b04-5475-bc83-a0758b31100f
-- title:
--   Tate's full faithfulness over mathcal O_K, points form
-- statement:
--   Let $p$ be a prime, let $K$ be an intermediate field of $\mathbb Q_p \subseteq \overline{\mathbb Q}_p$ that is finite over $\mathbb Q_p$, and write $\mathcal O =$ [`PadicAlgCl.ringOfIntegers p K`](def/PadicAlgCl_RingOfIntegers.html#L11), the intersection of the integral closure of $\mathbb Z_p$ in $\overline{\mathbb Q}_p$ with $K$. Let $G$ and $H$ be $p$-divisible groups over $\mathcal O$ of heights $h$ and $h'$: families of commutative rings `level v` carrying cocommutative Hopf algebra structures over $\mathcal O$, finite and free as $\mathcal O$-modules of rank $p^{vh}$ (resp. $p^{vh'}$), equipped with surjective bialgebra transition maps `level (v+1) → level v` whose kernels are the $p^v$-torsion ideals. For a commutative $\mathcal O$-algebra $L$, the level-$v$ points `G.Point L v` are the $\mathcal O$-algebra maps `G.level v →ₐ[𝒪] L` with the convolution group law, and `G.Points L` is the direct limit of the additive groups of these along the inclusions, with `G.pointsMkAdd` the canonical maps into the limit. Given an additive map $F$ from $G$'s points over $\overline{\mathbb Q}_p$ to $H$'s points over $\overline{\mathbb Q}_p$ such that (i) for every $v$ and every $x \in$ `G.Point (PadicAlgCl p) v` the element $F$ of the class of $x$ is the class of some $y \in$ `H.Point (PadicAlgCl p) v`, and (ii) $F$ commutes with the action of every $\mathcal O$-algebra automorphism $\tau$ of $\overline{\mathbb Q}_p$, the conclusion asserts the existence of a family of bialgebra maps $\varphi_v : H.\mathrm{level}\,v \to G.\mathrm{level}\,v$ over $\mathcal O$ such that $\mathrm{transition}^G_v \circ \varphi_{v+1} = \varphi_v \circ \mathrm{transition}^H_v$ for all $v$, such that for all $v$ and all $x \in$ `G.Point (PadicAlgCl p) v` the image $F$ of the class of $x$ is the class of the level-$v$ point of $H$ given by $\varphi_v$ followed by the algebra map underlying $x$, and such that any family $\varphi'$ of bialgebra maps satisfying this same identity on points equals $\varphi$. The uniqueness clause thus requires of $\varphi'$ only the identity on points, not compatibility with the transition maps.
--
--   This is Tate's full faithfulness theorem for $p$-divisible groups over the ring of integers of a finite extension of $\mathbb Q_p$, stated in terms of geometric points: level-preserving, Galois-equivariant additive maps on points come from a unique compatible family of bialgebra maps in the other direction. It is the special case from which the version over a complete discrete valuation ring lying over $p$, [`PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime`](thm.html#PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime), is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h h' : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (H : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
    (F : G.Points (PadicAlgCl p) →+ H.Points (PadicAlgCl p))

    (hFlev : ∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v), ∃ y : H.Point (PadicAlgCl p) v,
      F (G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul x)) = H.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul y))

    (hFgal : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (z : G.Points (PadicAlgCl p)), F (τ • z) = τ • F z) :
    ∃ φ : ∀ v : ℕ, H.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v,
      (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (H.transition v)) ∧
      (∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v),
        F (G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul x)) =
          H.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v))))) ∧

      (∀ φ' : ∀ v : ℕ, H.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v,
        (∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v),
          F (G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul x)) =
            H.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v))))) →
        φ' = φ) := by sorry
