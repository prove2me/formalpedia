-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_proper
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:08:30.757283+00:00
-- url     : https://prove2.me/theorems/74726bc9-14d6-49f5-beee-e60157ccc104
-- title:
--   Tanner Lifted Product: lps Original Special Fibre To Prime Field proper
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Special Fibre To Prime Field proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L166-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialHecke.lean#L166-L171

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.SchemeFrobenius
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreToPrimeField_proper
    (l N : ℕ) [Fact l.Prime] [NeZero N] (hN : 0 < N) :
    IsProper (lpsOriginalSpecialFibreToPrimeField l N hN) := by sorry
