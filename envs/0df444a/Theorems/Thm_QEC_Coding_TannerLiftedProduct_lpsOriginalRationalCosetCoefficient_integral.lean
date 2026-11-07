-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalCosetCoefficient_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCosetCoefficient_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:16:20.023441+00:00
-- url     : https://prove2.me/theorems/5b815d68-14f0-4cf6-855a-a6be31bfc107
-- title:
--   Tanner Lifted Product: lps Original Rational Coset Coefficient integral
-- statement:
--   True nome-germ comparison and triangular recovery prove every actual rational modular coefficient integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L835-L921
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L835-L921

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCosetCoefficient_integral
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
    (k n : ℕ) : IsIntegral ℤ (((Φ.coeff k).coeff n:ℚ):ℂ) := by sorry
