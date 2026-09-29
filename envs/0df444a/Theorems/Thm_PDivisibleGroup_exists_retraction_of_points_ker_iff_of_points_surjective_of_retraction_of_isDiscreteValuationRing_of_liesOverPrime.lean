-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_retraction_of_points_ker_iff_of_points_surjective_of_retraction_of_isDiscreteValuationRing_of_liesOverPrime
-- name    : PDivisibleGroup.exists_retraction_of_points_ker_iff_of_points_surjective_of_retraction_of_isDiscreteValuationRing_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/87151abb-16f5-5a24-adde-c329fde95932
-- title:
--   Transfer of splitness between two quotient witnesses of a p-divisible group
-- statement:
--   Let $p$ be a prime and let $Pl$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` with $p$ a non-unit of $Pl$ (this is `LiesOverPrime`). Let $Rh$ be a commutative domain which is a henselian local ring and a discrete valuation ring, equipped with an algebra map to $\overline{\mathbb Q}$ that is injective, whose image lies in $Pl$ and for which the maximal ideal of $Rh$ consists exactly of the elements whose image has $Pl$-valuation $<1$; $Rh$ is also a $\mathbb Z/p$-algebra, the structure map killing exactly those same elements. Let $\mathcal G$, $\mathcal B$, $\mathcal B_0$ be $p$-divisible groups over $Rh$ of heights $h$, $h_B$, $h_{B_0}$ in the sense of the project structure: families of finite free $Rh$-Hopf algebras `level v`, cocommutative, of rank $p^{vh}$, with surjective transition bialgebra maps `level (v+1) → level v` whose kernels are the $p^v$-torsion ideals (the image of the augmentation ideal under multiplication by $p^v$). Let $\psi_v \colon \mathcal B.\mathrm{level}\,v \to \mathcal G.\mathrm{level}\,v$ and $\psi^0_v \colon \mathcal B_0.\mathrm{level}\,v \to \mathcal G.\mathrm{level}\,v$ be bialgebra maps commuting with the transitions, i.e. $\mathcal G.\mathrm{transition}_v \circ \psi_{v+1} = \psi_v \circ \mathcal B.\mathrm{transition}_v$ and likewise for $\psi^0$. Points are $\overline{\mathbb Q}$-algebra maps out of the levels, with the convolution group structure. Assume that for each $v$ and each point $x$ of $\mathcal G$ at level $v$, the point $x \circ \psi_v$ of $\mathcal B$ is trivial if and only if the point $x \circ \psi^0_v$ of $\mathcal B_0$ is trivial; assume moreover that $x \mapsto x \circ \psi_v$ and $x \mapsto x \circ \psi^0_v$ are surjective onto the $\overline{\mathbb Q}$-points of $\mathcal B$ and of $\mathcal B_0$ at each level. Assume finally that each $\psi^0_v$ admits an $Rh$-linear retraction, that is, an $Rh$-linear $r \colon \mathcal G.\mathrm{level}\,v \to \mathcal B_0.\mathrm{level}\,v$ with $r(\psi^0_v b) = b$ for all $b$. Then each $\psi_v$ admits an $Rh$-linear retraction as well.
--
--   The statement transfers the $Rh$-module splitness of one quotient presentation of a $p$-divisible group to another presentation with the same kernel and image on $\overline{\mathbb Q}$-points, via Tate's full faithfulness over a henselian discrete valuation ring (invoked in the form [`PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime`](thm.html#PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime)). It is used in the injectivity statement for the map on Raynaud quotients attached to the Néron model of a modular curve at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_retraction_of_points_ker_iff_of_points_surjective_of_retraction_of_isDiscreteValuationRing_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.exists_retraction_of_points_ker_iff_of_points_surjective_of_retraction_of_isDiscreteValuationRing_of_liesOverPrime
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh] [IsDiscreteValuationRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h hB hB₀ : ℕ} (𝒢 : PDivisibleGroup Rh p h) (ℬ : PDivisibleGroup Rh p hB) (ℬ₀ : PDivisibleGroup Rh p hB₀)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v) (ψ₀ : ∀ v : ℕ, ℬ₀.level v →ₐc[Rh] 𝒢.level v)
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψ₀t : ∀ v : ℕ, (𝒢.transition v).comp (ψ₀ (v + 1)) = (ψ₀ v).comp (ℬ₀.transition v))

    (hker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ₀ v : ℬ₀.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ₀.Point (AlgebraicClosure ℚ) v))

    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b)
    (hψ₀surj : ∀ (v : ℕ) (b : ℬ₀.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ₀ v : ℬ₀.level v →ₐ[Rh] 𝒢.level v)) = b)

    (hr₀ : ∀ v : ℕ, ∃ r : 𝒢.level v →ₗ[Rh] ℬ₀.level v, ∀ b : ℬ₀.level v, r (ψ₀ v b) = b) :
    ∀ v : ℕ, ∃ r : 𝒢.level v →ₗ[Rh] ℬ.level v, ∀ b : ℬ.level v, r (ψ v b) = b := by sorry
