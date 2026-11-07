-- Prove2me | Theorems.Thm_QEC_Distillation_coordinateSupport_eq_taggedTriple
-- name    : QEC.Distillation.coordinateSupport_eq_taggedTriple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:11:57.632063+00:00
-- url     : https://prove2.me/theorems/6ea1d0d8-0a5d-4e08-af54-5e1ef1f90de4
-- title:
--   Distillation: coordinate Support eq tagged Triple
-- statement:
--   One coordinate support is literally the three tags above one site.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L28-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/PhysicalCCZ.lean#L28-L35

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped BigOperators
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]

theorem QEC.Distillation.coordinateSupport_eq_taggedTriple [Fintype ι] [DecidableEq ι]
    (site : ι) :
    coordinateSupport site =
      {(ThreeCopyTag.first, site), (ThreeCopyTag.second, site),
        (ThreeCopyTag.third, site)} := by sorry
