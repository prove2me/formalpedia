-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIndex_stabilizer_some_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_stabilizer_some_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:46.71986+00:00
-- url     : https://prove2.me/theorems/adeffd29-0330-4f49-9a49-6e0273868680
-- title:
--   Tanner Lifted Product: lps Hecke Index stabilizer some zero
-- statement:
--   The finite-action zero stabilizer is the actual second intersection inside original Gamma0(N).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L131-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean#L131-L141

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_stabilizer_some_zero (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.stabilizer (CongruenceSubgroup.Gamma0 N)
      (some ⟨0,(Fact.out:p.Prime).pos⟩:Option (Fin p)) =
      (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N) := by sorry
