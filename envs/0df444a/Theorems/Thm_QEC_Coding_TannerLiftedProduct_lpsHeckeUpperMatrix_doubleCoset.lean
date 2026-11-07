-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperMatrix_doubleCoset
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeUpperMatrix_doubleCoset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:14.544233+00:00
-- url     : https://prove2.me/theorems/e6cc097c-88f4-4fc3-906f-2c2b054e4640
-- title:
--   Tanner Lifted Product: lps Hecke Upper Matrix double Coset
-- statement:
--   Explicit integral Gamma0 factors put every representative in the same double coset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L144-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L144-L206

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeUpperMatrix_doubleCoset (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (i : Option (Fin p)) :
    ∃ (δ γ : SL(2,ℤ)), δ∈CongruenceSubgroup.Gamma0 N ∧ γ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p i=(δ:Matrix (Fin 2) (Fin 2) ℤ)*
        lpsHeckeUpperMatrix p none*(γ:Matrix (Fin 2) (Fin 2) ℤ) := by sorry
