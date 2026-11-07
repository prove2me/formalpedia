-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_spec
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:21.151205+00:00
-- url     : https://prove2.me/theorems/7461b326-9b29-4167-84a6-a23d46721914
-- title:
--   Tanner Lifted Product: lps Hecke Right Index spec
-- statement:
--   The selected index has a genuine integral Gamma0 factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L262-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L262-L267

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_spec (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    ∃ δ : SL(2,ℤ), δ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
        (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p (lpsHeckeRightIndex N p hNp γ hγ i) := by sorry
