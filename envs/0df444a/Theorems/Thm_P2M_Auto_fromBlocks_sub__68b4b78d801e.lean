-- Prove2me | Theorems.Thm_P2M_Auto_fromBlocks_sub__68b4b78d801e
-- name    : P2M_Auto_fromBlocks_sub__68b4b78d801e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:43.931614+00:00
-- url     : https://prove2.me/theorems/4024d829-e974-428e-a7f7-1bb061f4b77d
-- title:
--   P2 M Auto from Blocks sub  68b4b78d801e: P2 M Auto from Blocks sub  68b4b78d801e
-- statement:
--   The P2 M Auto from Blocks sub  68b4b78d801e construction uses the P2 M Auto from Blocks sub  68b4b78d801e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3578-L3581
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3578-L3581

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_Auto_fromBlocks_sub__68b4b78d801e (a b c d a' b' c' d' : Matrix ι ι ℂ) :
    Matrix.fromBlocks a b c d - Matrix.fromBlocks a' b' c' d' = Matrix.fromBlocks (a - a') (b -
      b') (c - c') (d - d') := by sorry

alias «Auto».«fromBlocks_sub'» := P2M_Auto_fromBlocks_sub__68b4b78d801e
