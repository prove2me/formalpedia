-- Prove2me | Theorems.Thm_QEC_Locality_fixedGeneratorDecoupled_symm
-- name    : QEC.Locality.fixedGeneratorDecoupled_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:38.03234+00:00
-- url     : https://prove2.me/theorems/9237f32b-6929-4f25-a279-f17f0436b2ac
-- title:
--   Locality: fixed Generator Decoupled symm
-- statement:
--   A small helper for reversing a fixed-generator decoupling certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L533-L540
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L533-L540

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK

theorem QEC.Locality.fixedGeneratorDecoupled_symm
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {left right : Set ι}
    (h : P.fixedGeneratorDecoupled left right) :
    P.fixedGeneratorDecoupled right left := by sorry
