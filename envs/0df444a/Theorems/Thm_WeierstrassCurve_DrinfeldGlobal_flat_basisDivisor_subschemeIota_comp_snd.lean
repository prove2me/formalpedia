-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_flat_basisDivisor_subschemeIota_comp_snd
-- name    : WeierstrassCurve.DrinfeldGlobal.flat_basisDivisor_subschemeIota_comp_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/39a125c9-d63a-51f0-8d3d-e60407d15e9d
-- title:
--   Flatness of the Drinfeld basis divisor over the base
-- statement:
--   Let $T$ be a commutative ring and $W$ a Weierstrass curve over $T$ whose discriminant $W.\Delta$ is a unit; write $W$ also for the associated projective Weierstrass curve and let $\pi =$ `projModelStrCR W` be the structure morphism $\mathrm{Proj}$ of the graded quotient ring of the Weierstrass cubic $\to \mathrm{Spec}\,T$. Let $G$ be a relative group law on $\pi$, that is, functorially compatible multiplication, unit and inverse operations on the sets of $\pi$-sections over arbitrary $T$-schemes satisfying the group axioms; let $n$ be a natural number and let $P, Q$ be sections of $\pi$ over the identity of $\mathrm{Spec}\,T$ (morphisms $\mathrm{Spec}\,T \to \mathrm{Proj}$ composing with $\pi$ to the identity). Consider the ideal sheaf data `basisDivisor G n P Q` on the fibre product of $\pi$ with the identity of $\mathrm{Spec}\,T$, defined as the product over $i \in \mathrm{Fin}(n\cdot n)$ of the kernel ideal sheaves of the graphs of the $G$-linear combinations $\lfloor i/n\rfloor\cdot P + (i \bmod n)\cdot Q$. The assertion is that the closed immersion of the associated closed subscheme, followed by the second projection of that fibre product, is flat.
--
--   This records that the divisor $\sum_{0\le a,b<n}[aP+bQ]$ cut out on the elliptic curve by a pair of sections and a group law is flat over the base, the flatness condition entering the notion of a Drinfeld $\Gamma(n)$-basis. It is used in the extension statement [`WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map`](thm.html#WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_flat_basisDivisor_subschemeIota_comp_snd.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.flat_basisDivisor_subschemeIota_comp_snd
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (G : RelativeGroupLaw T (projModelStrCR W)) (n : ℕ) (P Q : Section W) :
    Flat ((basisDivisor G n P Q).subschemeι ≫ pullback.snd (projModelStrCR W) (𝟙 (Spec (CommRingCat.of T)))) := by sorry
