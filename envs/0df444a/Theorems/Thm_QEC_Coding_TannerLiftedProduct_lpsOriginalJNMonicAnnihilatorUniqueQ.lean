-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNMonicAnnihilatorUniqueQ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNMonicAnnihilatorUniqueQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:08:40.677643+00:00
-- url     : https://prove2.me/theorems/c2c820e3-e591-474d-a5c4-8b9b5f0dea50
-- title:
--   Tanner Lifted Product: lps Original JNMonic Annihilator Unique Q
-- statement:
--   Uniqueness of a monic rational annihilator within the actual coset degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L46-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L46-L61

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNMonicAnnihilatorUniqueQ
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ P : Polynomial (FractionRing (Polynomial ℚ)), P.Monic →
      P.natDegree ≤ Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) →
      Polynomial.aeval (lpsOriginalJNInFractionField N hN) P = 0 →
      P = minpoly (FractionRing (Polynomial ℚ))
        (lpsOriginalJNInFractionField N hN) := by sorry
