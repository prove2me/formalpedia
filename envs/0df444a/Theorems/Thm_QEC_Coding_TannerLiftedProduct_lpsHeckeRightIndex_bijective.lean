-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_bijective
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:21.203377+00:00
-- url     : https://prove2.me/theorems/a56b9b42-4f3e-483e-9152-376a2e317b6c
-- title:
--   Tanner Lifted Product: lps Hecke Right Index bijective
-- statement:
--   The actual right-index map is a permutation of the finite representative set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L292-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L292-L304

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeRightIndex_bijective (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) :
    Function.Bijective (lpsHeckeRightIndex N p hNp γ hγ) := by sorry
