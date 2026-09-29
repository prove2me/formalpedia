-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_section_comp_eq_of_isFractionRing
-- name    : WeierstrassCurve.DrinfeldGlobal.existsUnique_section_comp_eq_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/8882cc1d-ea81-5429-9452-dd53e4b563b1
-- title:
--   Unique extension of K-points of the projective Weierstrass model over a DVR
-- statement:
--   Let $R_0$ be a discrete valuation ring (a commutative ring that is a domain and a discrete valuation ring), let $K$ be a field equipped with an $R_0$-algebra structure making it a fraction field of $R_0$, and let $W_0$ be a Weierstrass curve over $R_0$. Write $\mathrm{projModelCR}\,W_0$ for the projective model of $W_0$, namely $\mathrm{Proj}$ of the grading on the quotient of the polynomial ring in three variables by the homogeneous ideal cut out by the Weierstrass cubic, and $\mathrm{projModelStrCR}\,W_0$ for its structure morphism to $\mathrm{Spec}\,R_0$, given by $\mathrm{Proj.toSpecZero}$ followed by $\mathrm{Spec}$ of the map from $R_0$ to the degree-zero part. Let $s : \mathrm{Spec}\,K \to \mathrm{projModelCR}\,W_0$ be a morphism of schemes such that $s$ followed by $\mathrm{projModelStrCR}\,W_0$ equals $\mathrm{Spec}$ of the structure map $R_0 \to K$. Then there is exactly one element $P_0$ of $\mathrm{Section}\,W_0$, that is, exactly one pair consisting of a morphism $\mathrm{Spec}\,R_0 \to \mathrm{projModelCR}\,W_0$ together with a proof that this morphism followed by $\mathrm{projModelStrCR}\,W_0$ is the identity of $\mathrm{Spec}\,R_0$, whose underlying morphism satisfies: $\mathrm{Spec}$ of $R_0 \to K$ followed by it equals $s$.
--
--   This is the valuative criterion of properness applied to the projective Weierstrass model: every $K$-point of the model over a discrete valuation ring $R_0$ with fraction field $K$ comes from a unique $R_0$-section, no nondegeneracy hypothesis on the cubic being needed. It is used to extend the two sections of a raw Drinfeld pair from the generic fibre to the model over $R_0$, in [`WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map`](thm.html#WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_section_comp_eq_of_isFractionRing.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.existsUnique_section_comp_eq_of_isFractionRing
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀)
    (s : Spec (CommRingCat.of K) ⟶ projModelCR W₀)
    (hs : s ≫ projModelStrCR W₀ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K))) :
    ∃! P₀ : Section W₀, Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) ≫ P₀.1 = s := by sorry
