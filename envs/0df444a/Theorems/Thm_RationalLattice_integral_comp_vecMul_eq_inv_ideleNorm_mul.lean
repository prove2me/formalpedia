-- Prove2me | Theorems.Thm_RationalLattice_integral_comp_vecMul_eq_inv_ideleNorm_mul
-- name    : RationalLattice.integral_comp_vecMul_eq_inv_ideleNorm_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/5e6e88fa-8321-51a7-9602-26388cc60405
-- title:
--   Right GL₃ translation scales finite-adelic integrals by inverse idele norm
-- statement:
--   Write $F$ for the finite adele ring `FiniteAdeleRing (𝓞 ℚ) ℚ` of $\mathbb{Q}$, and equip the space $F^{3}$ of functions $\mathrm{Fin}\ 3 \to F$ with a measurable structure that is the Borel structure of its topology. Let $\mu$ be a measure on $F^{3}$ which is an additive Haar measure and is regular, let $m$ be an element of the general linear group $\mathrm{GL}_3(F)$, and let $h : F^{3} \to \mathbb{C}$ be an arbitrary function, with no integrability or measurability hypothesis imposed. Then the Bochner integral of the function $x \mapsto h(x\,m)$ against $\mu$, where $x\,m$ denotes `Matrix.vecMul` of the row vector $x$ by the underlying $3 \times 3$ matrix of $m$, equals the inverse in $\mathbb{C}$ of the real number $\mathrm{ideleNorm}_{\mathbb{Q}}$ of the unit $\mathrm{Units.map}\ \mathrm{finIncl}\ (\det m)$, times the Bochner integral of $h$ against $\mu$. Here $\det m$ is the determinant of $m$ as a unit of $F$, `AdelicLevel.finIncl` sends a finite adele $y$ to the adele $(1, y)$ with archimedean component $1$, and for a unit $x$ of the adele ring of $\mathbb{Q}$, `TateGlobal.ideleNorm ℚ x` is the value at $x$ of the distributive Haar character `distribHaarChar` of the adele ring, viewed as a real number.
--
--   This is the finite-adelic change-of-variables formula for the right action of $\mathrm{GL}_3$ on $F^{3}$: the modulus of the linear automorphism $x \mapsto x\,m$ is the idele norm of the determinant of $m$, so integration against an additive Haar measure rescales by its inverse, exactly as $\int h(xm)\,dx = |\det m|^{-1}\int h$ over a Euclidean space. It is used in the construction of adelic Epstein-type series occurring in the cubic-induction step towards the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RationalLattice_integral_comp_vecMul_eq_inv_ideleNorm_mul.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

theorem RationalLattice.integral_comp_vecMul_eq_inv_ideleNorm_mul [MeasurableSpace (Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ)]
    [BorelSpace (Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ)] (μ : Measure (Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure]
    [μ.Regular] (m : Matrix.GeneralLinearGroup (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (h : (Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ) :
    ∫ x, h (Matrix.vecMul x (m : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ))) ∂μ =
      ((TateGlobal.ideleNorm ℚ (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (Matrix.GeneralLinearGroup.det m)) : ℝ) :
          ℂ)⁻¹ *
        ∫ x, h x ∂μ := by sorry
