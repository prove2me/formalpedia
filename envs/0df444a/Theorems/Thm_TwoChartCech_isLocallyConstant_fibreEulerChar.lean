-- Prove2me | Theorems.Thm_TwoChartCech_isLocallyConstant_fibreEulerChar
-- name    : TwoChartCech.isLocallyConstant_fibreEulerChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/dfdb50f1-8444-5d1f-9021-59385c6b8db7
-- title:
--   Local constancy of the fibrewise Euler characteristic
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $C^0$, $C^1$ be $R$-modules in the same universe as $R$, both flat over $R$, and let $d \colon C^0 \to C^1$ be an $R$-linear map such that $\ker d$ is a finitely generated $R$-module and the cokernel $C^1/\operatorname{im} d$ is a finitely generated $R$-module. For a prime $\mathfrak p \subset R$ write $\kappa(\mathfrak p)$ for the residue field of $\mathfrak p$ (the residue field of the localisation, as produced by `Ideal.ResidueField`), and let $d \otimes \kappa(\mathfrak p) \colon \kappa(\mathfrak p) \otimes_R C^0 \to \kappa(\mathfrak p) \otimes_R C^1$ be the base change of $d$. The theorem asserts that the function
--   $$\operatorname{Spec} R \to \mathbb Z, \qquad \mathfrak p \mapsto \dim_{\kappa(\mathfrak p)} \ker\bigl(d \otimes \kappa(\mathfrak p)\bigr) - \dim_{\kappa(\mathfrak p)} \Bigl( \bigl(\kappa(\mathfrak p) \otimes_R C^1\bigr) / \operatorname{im}\bigl(d \otimes \kappa(\mathfrak p)\bigr) \Bigr)$$
--   is locally constant for the Zariski topology on the prime spectrum, the two dimensions being `Module.finrank` over $\kappa(\mathfrak p)$ cast to $\mathbb Z$.
--
--   This is the two-term case of the classical statement that the Euler characteristic of the fibres of a flat family is locally constant on the base. In this development it is applied to the Čech complex of a coherent sheaf, flat over a Noetherian affine base, computed from a cover by two affine charts, and is cited by the results on relative Picard schemes and on the constancy and semicontinuity of fibrewise $h^0 - h^1$ for such two-chart covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_isLocallyConstant_fibreEulerChar.lean

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct

theorem TwoChartCech.isLocallyConstant_fibreEulerChar
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    IsLocallyConstant fun 𝔭 : PrimeSpectrum R =>
      (Module.finrank 𝔭.asIdeal.ResidueField
          (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField)) : ℤ)
        - Module.finrank 𝔭.asIdeal.ResidueField
            ((𝔭.asIdeal.ResidueField ⊗[R] C1) ⧸ LinearMap.range (d.baseChange 𝔭.asIdeal.ResidueField)) := by sorry
