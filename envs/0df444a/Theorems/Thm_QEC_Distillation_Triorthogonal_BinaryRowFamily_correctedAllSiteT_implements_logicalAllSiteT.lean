-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_implements_logicalAllSiteT
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_implements_logicalAllSiteT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:53:16.639551+00:00
-- url     : https://prove2.me/theorems/af631e4f-4dd0-4014-927b-e929a59685e6
-- title:
--   Binary Row Family: corrected All Site T implements logical All Site T
-- statement:
--   The exact corrected BH12 transversal implementation equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2739-L2752
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2739-L2752

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
universe v

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_implements_logicalAllSiteT
    {LogicalRow PhysicalCol : Type u} {StabilizerRow : Type v}
    [Fintype LogicalRow] [Fintype StabilizerRow] [Fintype PhysicalCol]
    [DecidableEq LogicalRow] [DecidableEq StabilizerRow] [DecidableEq PhysicalCol]
    (R : BinaryRowFamily LogicalRow StabilizerRow PhysicalCol)
    (hR : R.IsTriorthogonal) :
    (R.encodedCode hR).ImplementsLogicalGate R.correctedAllSiteT
      (allSiteT (Index := LogicalRow)) := by sorry
