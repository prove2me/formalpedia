-- Prove2me | Theorems.Thm_QseriesFormalization_Ch01_partitionCount_zero
-- name    : QseriesFormalization.Ch01.partitionCount_zero
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T08:50:20.029338+00:00
-- url     : https://prove2.me/theorems/dc1f16cb-bd29-4064-8e9e-946d738c4cad
-- title:
--   $p(0)=1$
-- statement:
--   The number of partitions of $0$ is $1$:
--   $$p(0)=1.$$
--   This is the base case of the partition-number computations in Chapter 1.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 1. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter01.lean#L6428-L6430

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib

/-!
# Chapter 1: Introduction

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 1.)

Most of the introductory material—partitions, triangular numbers,
the q-Pochhammer symbol—lives in `QseriesFormalization.Basic`.
This file collects any chapter-specific lemmas that are too lightweight
to belong in `Basic.lean` but that the introduction relies on.

Currently empty; populated as we work through Chapter 1.
-/

open QseriesFormalization
open QseriesFormalization.Ch01

theorem QseriesFormalization.Ch01.partitionCount_zero : partitionCount 0 = 1 := by sorry
