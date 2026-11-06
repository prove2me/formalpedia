-- Prove2me | Theorems.Thm_QEC_Bounds_BPTQuditLattice_erasureChannel_specification
-- name    : QEC.Bounds.BPTQuditLattice.erasureChannel_specification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:08:37.980234+00:00
-- url     : https://prove2.me/theorems/c19d1951-10a0-462f-ba4d-3fa4725e1f5a
-- title:
--   BPTQudit Lattice: erasure Channel specification
-- statement:
--   The lattice-region erasure channel is exactly the concrete subsystem channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L97-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Model.lean#L97-L99

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannel_specification

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTQuditLattice

theorem QEC.Bounds.BPTQuditLattice.erasureChannel_specification (L : BPTQuditLattice) (region : Finset L.Site) :
    L.erasureChannel region = (L.subsystem region).erasureChannelFromRegister := by sorry
