-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSCheckSet_subset_generatedGroup
-- name    : QEC.Coding.PauliSymplectic.binaryCSSCheckSet_subset_generatedGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:40:28.167178+00:00
-- url     : https://prove2.me/theorems/55191592-b38b-45ba-80b5-0d39579577bd
-- title:
--   Pauli Symplectic: binary CSSCheck Set subset generated Group
-- statement:
--   Every declared binary CSS check belongs to the independently generated group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L93-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/SourceValidity.lean#L93-L100

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.binaryCSSCheckSet_subset_generatedGroup
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    binaryCSSCheckSet xCode zCode ≤
      (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).generatedGroup := by sorry
