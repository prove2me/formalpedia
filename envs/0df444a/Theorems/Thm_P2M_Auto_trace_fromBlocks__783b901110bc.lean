-- Prove2me | Theorems.Thm_P2M_Auto_trace_fromBlocks__783b901110bc
-- name    : P2M_Auto_trace_fromBlocks__783b901110bc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:18.504203+00:00
-- url     : https://prove2.me/theorems/f7adaf5b-8fb8-40a4-8b52-696d8da281d8
-- title:
--   P2 M Auto trace from Blocks  783b901110bc: P2 M Auto trace from Blocks  783b901110bc
-- statement:
--   The P2 M Auto trace from Blocks  783b901110bc construction uses the P2 M Auto trace from Blocks  783b901110bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3481-L3483
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3481-L3483

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem P2M_Auto_trace_fromBlocks__783b901110bc (a b c d : Matrix ι ι ℂ) :
    (Matrix.fromBlocks a b c d).trace = a.trace + d.trace := by sorry

alias «Auto».«trace_fromBlocks'» := P2M_Auto_trace_fromBlocks__783b901110bc
