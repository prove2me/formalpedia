-- Prove2me | Theorems.Thm_QEC_Distillation_taggedCoordinate_mem_coordinateSupport
-- name    : QEC.Distillation.taggedCoordinate_mem_coordinateSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:44:03.489251+00:00
-- url     : https://prove2.me/theorems/ea5c173b-0fff-43c9-bea1-b64b6466cb3a
-- title:
--   Distillation: tagged Coordinate mem coordinate Support
-- statement:
--   Every tag appears in the support of its corresponding within-copy site.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Register.lean#L110-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Register.lean#L110-L113

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
universe u
variable {F ι : Type u} [Field F] [Fintype F]

theorem QEC.Distillation.taggedCoordinate_mem_coordinateSupport [Fintype ι] [DecidableEq ι]
    (tag : ThreeCopyTag) (site : ι) :
    (tag, site) ∈ coordinateSupport site := by sorry
