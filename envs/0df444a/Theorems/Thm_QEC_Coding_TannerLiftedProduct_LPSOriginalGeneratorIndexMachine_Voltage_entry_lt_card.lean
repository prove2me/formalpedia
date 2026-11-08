-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_Voltage_entry_lt_card
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.entry_lt_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:57:53.431088+00:00
-- url     : https://prove2.me/theorems/8fc52a0d-daae-40fd-905e-508db1197bfb
-- title:
--   Voltage: entry lt card
-- statement:
--   Every computed voltage table entry is below the genuine original PSL cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L130-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean#L130-L138

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage._p2m_local_instance_ef31e85fec_23

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage.entry_lt_card {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) (v:ℕ) (hv:v∈entries a ts):
 v<Fintype.card PSL(2,ZMod a.q):= by sorry
