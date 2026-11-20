-- Prove2me | Theorems.Thm_P2M_Aggmetrics_DataStream_natAbs_sub_of_lt__f4533c285d97
-- name    : P2M_Aggmetrics_DataStream_natAbs_sub_of_lt__f4533c285d97
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:31.393533+00:00
-- url     : https://prove2.me/theorems/c8d5e5c3-a23b-4b72-8369-a21ad0e7c336
-- title:
--   P2 M Aggmetrics Data Stream nat Abs sub of lt  f4533c285d97: P2 M Aggmetrics Data Stream nat Abs sub of lt  f4533c285d97
-- statement:
--   The P2 M Aggmetrics Data Stream nat Abs sub of lt  f4533c285d97 construction uses the P2 M Aggmetrics Data Stream nat Abs sub of lt  f4533c285d97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L67-L70
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean#L67-L70

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream

theorem P2M_Aggmetrics_DataStream_natAbs_sub_of_lt__f4533c285d97 {i t : ℕ} (h : i < t) : Int.natAbs ((t : ℤ) - (i : ℤ)) = t - i := by sorry

alias «Aggmetrics».«DataStream».«natAbs_sub_of_lt'» := P2M_Aggmetrics_DataStream_natAbs_sub_of_lt__f4533c285d97
