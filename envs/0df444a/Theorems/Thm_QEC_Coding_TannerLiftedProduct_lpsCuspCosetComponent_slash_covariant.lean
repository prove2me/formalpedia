-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetComponent_slash_covariant
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetComponent_slash_covariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:24.418959+00:00
-- url     : https://prove2.me/theorems/7869ad93-74f8-4583-8074-fe951cf79c78
-- title:
--   Tanner Lifted Product: lps Cusp Coset Component slash covariant
-- statement:
--   Slash transformation permutes the actual induced cusp components.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L451-L458
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L451-L458

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetComponent_slash_covariant (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (lpsCuspCosetComponent N f (h • γ)) ∣[(2:ℤ)] h=lpsCuspCosetComponent N f γ := by sorry
