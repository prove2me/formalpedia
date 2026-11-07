-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_inverse
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:25.046083+00:00
-- url     : https://prove2.me/theorems/9e662c24-1cf7-420a-a598-198ad06989be
-- title:
--   Tanner Lifted Product: lps Hecke Right Index inverse
-- statement:
--   Right multiplication by the inverse recovers the original representative index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L270-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L270-L289

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_inverse (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp γ⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hγ)
      (lpsHeckeRightIndex N p hNp γ hγ i)=i := by sorry
