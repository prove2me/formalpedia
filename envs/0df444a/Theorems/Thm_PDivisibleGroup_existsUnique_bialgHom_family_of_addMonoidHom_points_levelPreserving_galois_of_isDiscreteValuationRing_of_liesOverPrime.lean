-- Prove2me | Theorems.Thm_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
-- name    : PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/18201717-8f42-52c3-bb06-020e0f2b63fb
-- title:
--   Tate full faithfulness over a henselian place ring of ℚ̄
-- statement:
--   Let $p$ be a prime and let $Pl$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` satisfying `Pl.LiesOverPrime p`, i.e. the image of $p$ is a nonunit of $Pl$. Let $Rh$ be a henselian local discrete valuation domain equipped with an algebra map to $\overline{\mathbb Q}$ whose associated scalar action is faithful, such that every $algebraMap$ image of $Rh$ lies in $Pl$ (hypothesis `hRA`), the maximal ideal of $Rh$ consists exactly of those $x$ whose image has $Pl$-valuation $< 1$ (`hRloc`), and which carries an algebra map to $\mathbb Z/p$ whose kernel is again that set (`hres`). Let $G$ and $H$ be $p$-divisible groups over $Rh$ of heights $h$ and $h'$: thus for each $v$ a commutative ring $G.level\,v$ which is a finite free $Rh$-module with cocommutative Hopf algebra structure, of $Rh$-rank $p^{vh}$, together with surjective bialgebra transition maps $G.level\,(v+1) \to G.level\,v$ whose kernel is the $p^v$-torsion ideal of the augmentation ideal, and similarly for $H$ with $p^{vh'}$. Let $F$ be an additive map from $G.Points\,\overline{\mathbb Q}$ to $H.Points\,\overline{\mathbb Q}$, where the group of points is the direct limit over $v$ of the additive groups underlying the convolution groups of $Rh$-algebra maps $level\,v \to \overline{\mathbb Q}$. Assume $F$ is level preserving, in the sense that for every $v$ and every $x \in G.Point\,\overline{\mathbb Q}\,v$ the image under $F$ of the class of $x$ is the class of some $y \in H.Point\,\overline{\mathbb Q}\,v$ (`hFlev`), and that $F$ commutes with the action of every $Rh$-algebra automorphism $\tau$ of $\overline{\mathbb Q}$ (`hFgal`). Then there exists a family of $Rh$-bialgebra maps $\varphi_v : H.level\,v \to G.level\,v$ such that $\varphi_{v+1}$ followed by the transition map of $G$ equals the transition map of $H$ followed by $\varphi_v$ for all $v$; such that for every $v$ and every $x \in G.Point\,\overline{\mathbb Q}\,v$ the image under $F$ of the class of $x$ is the class of the point obtained from the algebra map $\varphi_v$ followed by $x$; and such that any family $\varphi'_v$ of $Rh$-bialgebra maps $H.level\,v \to G.level\,v$ satisfying this last compatibility with $F$ (transition compatibility not being required of $\varphi'$) coincides with $\varphi$.
--
--   This is Tate's full faithfulness theorem for $p$-divisible groups, $\operatorname{Hom}_R(G,H) \cong \operatorname{Hom}_K(G_K,H_K)$, cast in the language of groups of geometric points and specialised to a henselian discrete valuation ring sitting inside $\overline{\mathbb Q}$, centred on a place above $p$ and with residue field $\mathbb F_p$. It is used in the construction of a retraction of $p$-divisible groups over such a base ring, which in turn serves the analysis at $p$ of the relevant Néron objects.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
    (p : ℕ) [Fact p.Prime]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh] [IsDiscreteValuationRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h h' : ℕ} (G : PDivisibleGroup Rh p h) (H : PDivisibleGroup Rh p h')
    (F : G.Points (AlgebraicClosure ℚ) →+ H.Points (AlgebraicClosure ℚ))

    (hFlev : ∀ (v : ℕ) (x : G.Point (AlgebraicClosure ℚ) v), ∃ y : H.Point (AlgebraicClosure ℚ) v,
      F (G.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y))

    (hFgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ) (z : G.Points (AlgebraicClosure ℚ)), F (τ • z) = τ • F z) :
    ∃ φ : ∀ v : ℕ, H.level v →ₐc[Rh] G.level v,
      (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (H.transition v)) ∧
      (∀ (v : ℕ) (x : G.Point (AlgebraicClosure ℚ) v),
        F (G.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) =
          H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[Rh] G.level v))))) ∧

      (∀ φ' : ∀ v : ℕ, H.level v →ₐc[Rh] G.level v,
        (∀ (v : ℕ) (x : G.Point (AlgebraicClosure ℚ) v),
          F (G.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) =
            H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[Rh] G.level v))))) →
        φ' = φ) := by sorry
