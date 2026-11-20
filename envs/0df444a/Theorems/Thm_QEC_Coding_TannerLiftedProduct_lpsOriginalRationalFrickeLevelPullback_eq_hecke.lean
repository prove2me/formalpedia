-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalFrickeLevelPullback_eq_hecke
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalFrickeLevelPullback_eq_hecke
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:56:18.760251+00:00
-- url     : https://prove2.me/theorems/b506cade-202f-4d37-b040-605be8cb4e08
-- title:
--   Tanner Lifted Product: lps Original Rational Fricke Level Pullback eq hecke
-- statement:
--   Fricke conjugation of the actual level inclusion is literally the original dilation map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L41-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean#L41-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalFrickeLevelPullback_eq_hecke
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
      (Nat.mul_pos hN hp) = lpsOriginalRationalHeckePullback N p hN hp h4N := by sorry
