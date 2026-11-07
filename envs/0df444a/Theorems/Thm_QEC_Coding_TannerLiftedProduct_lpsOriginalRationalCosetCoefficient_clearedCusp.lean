-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalCosetCoefficient_clearedCusp
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCosetCoefficient_clearedCusp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:15:20.084977+00:00
-- url     : https://prove2.me/theorems/5ac040b1-1d73-4569-a009-8b509a422443
-- title:
--   Tanner Lifted Product: lps Original Rational Coset Coefficient cleared Cusp
-- statement:
--   The actual complete rational coset product constructs an integral analytic cleared coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L761-L830
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L761-L830

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCosetCoefficient_clearedCusp
    (N : ℕ) [NeZero N] (hN : 0<N) (Φ : Polynomial (Polynomial ℚ))
    (hΦ : Φ.Monic)
    (hd : Φ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    (hp : letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
      ∀ τ : ℍ, Φ.map ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ)))=
        ∏ x : (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
          (Polynomial.X-Polynomial.C (lpsOriginalJDilated N hN (x.out.val⁻¹•τ))))
    (k : ℕ) :
    ∃ G : lpsOriginalCuspAnalyticSubring,
      (∀ n, IsIntegral ℤ ((lpsOriginalCuspTaylorRingHom G).coeff n)) ∧
      ∀ σ : ℍ, G.val (Function.Periodic.qParam 1 (σ:ℂ))=
        Function.Periodic.qParam 1 (σ:ℂ)^(N^2*(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)-k)) *
          ((Φ.coeff k).map (algebraMap ℚ ℂ)).eval (lpsOriginalJDilated N hN σ) := by sorry
