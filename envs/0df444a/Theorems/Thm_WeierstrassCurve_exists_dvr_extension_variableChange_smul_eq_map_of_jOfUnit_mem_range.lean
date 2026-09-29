-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range
-- name    : WeierstrassCurve.exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/0742cd3e-7379-5343-8d73-5153ae974cc2
-- title:
--   Potential good reduction over a DVR extension for integral j
-- statement:
--   Let $R_0$ be a commutative domain which is a discrete valuation ring, and let $K$ be a field equipped with an $R_0$-algebra structure realising $K$ as the fraction field of $R_0$ (both types in a fixed universe $u$). Let $W$ be a Weierstrass curve over $K$ whose discriminant $W.\Delta$ is a unit of $K$; the resulting elliptic curve has $j$-invariant `W.jOfUnit hΔ`, defined as $W.j$ computed using the ellipticity witnessed by that unit hypothesis, and it is assumed that this $j$-invariant lies in the image of the structure map $R_0 \to K$. The assertion is that there exist a field $K'$ with a $K$-algebra structure making it a finite extension of $K$, a commutative domain $A'$ which is a discrete valuation ring together with a $K'$-algebra structure realising $K'$ as its fraction field, and a ring homomorphism $f : R_0 \to A'$, such that: (i) $f$ followed by $A' \to K'$ agrees with $R_0 \to K$ followed by $K \to K'$; (ii) any $x \in K$ whose image in $K'$ lies in the image of $A' \to K'$ already lies in the image of $R_0 \to K$ (so that $A'$ cuts out exactly $R_0$ inside $K$); and (iii) there are a variable change $C'$ over $K'$ and a Weierstrass curve $W'$ over $A'$ with $W'.\Delta$ a unit of $A'$ such that $C'$ applied to the base change of $W$ along $K \to K'$ equals the base change of $W'$ along $A' \to K'$.
--
--   This is the criterion of potential good reduction for an elliptic curve with integral $j$-invariant, in the form of an explicit good model over a discrete valuation ring of a finite extension of $K$, and valid in every residue characteristic (including $2$, $3$ and the equal-characteristic case); the two residue-characteristic regimes are handled by the $2$-torsion and $3$-torsion good-model constructions, combined with the existence of a dominating discrete valuation ring in a finite extension. It feeds the corresponding statement for curves arising from $\Gamma_1$-points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.exists_dvr_extension_variableChange_smul_eq_map_of_jOfUnit_mem_range
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W : WeierstrassCurve K) (hΔ : IsUnit W.Δ)
    (hj : W.jOfUnit hΔ ∈ Set.range (algebraMap R₀ K)) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A' K') (_ : IsFractionRing A' K') (f : R₀ →+* A'),
      (algebraMap A' K').comp f = (algebraMap K K').comp (algebraMap R₀ K) ∧
      (∀ x : K, algebraMap K K' x ∈ Set.range (algebraMap A' K') → x ∈ Set.range (algebraMap R₀ K)) ∧
      ∃ (C' : WeierstrassCurve.VariableChange K') (W' : WeierstrassCurve A'),
        IsUnit W'.Δ ∧ C' • (W.map (algebraMap K K')) = W'.map (algebraMap A' K') := by sorry
