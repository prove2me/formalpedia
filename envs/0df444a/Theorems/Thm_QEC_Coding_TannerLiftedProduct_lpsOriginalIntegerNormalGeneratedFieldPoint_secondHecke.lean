-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGeneratedFieldPoint_secondHecke
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGeneratedFieldPoint_secondHecke
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:53:51.235454+00:00
-- url     : https://prove2.me/theorems/27ade92c-5dc0-45cd-842b-ed49f911268c
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Generated Field Point second Hecke
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Generated Field Point second Hecke property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L328-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L328-L338

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGeneratedFieldPoint_secondHecke
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerNormalGeneratedFieldPoint (N*p) (Nat.mul_pos hN hp) ≫
      lpsOriginalIntegerNormalGluedSecondLevelMap N (N*p) (dvd_mul_right N p) h4N hN
        (Nat.mul_pos hN hp) =
    Spec.map (CommRingCat.ofHom (lpsOriginalRationalHeckePullback N p hN hp h4N)) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by sorry
