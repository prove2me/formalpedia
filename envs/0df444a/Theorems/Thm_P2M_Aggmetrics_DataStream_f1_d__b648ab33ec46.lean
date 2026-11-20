-- Prove2me | Theorems.Thm_P2M_Aggmetrics_DataStream_f1_d__b648ab33ec46
-- name    : P2M_Aggmetrics_DataStream_f1_d__b648ab33ec46
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:31:06.923281+00:00
-- url     : https://prove2.me/theorems/69e43502-9f87-49fa-8b00-7d2277eadc3b
-- title:
--   P2 M Aggmetrics Data Stream f1 d  b648ab33ec46: P2 M Aggmetrics Data Stream f1 d  b648ab33ec46
-- statement:
--   `∂ F₁ / ∂π = 2R₁₁(1-R₀₀) / D²`.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L200-L210
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean#L200-L210

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream

theorem P2M_Aggmetrics_DataStream_f1_d__b648ab33ec46 (R S π : ℝ) (hD : π * (1 + R) + (1 - π) * (1 - S) ≠ 0) :
    HasDerivAt (fun y => f1 R S y)
      (2 * R * (1 - S) / (π * (1 + R) + (1 - π) * (1 - S)) ^ 2) π := by sorry

alias «Aggmetrics».«DataStream».«f1_dπ» := P2M_Aggmetrics_DataStream_f1_d__b648ab33ec46
