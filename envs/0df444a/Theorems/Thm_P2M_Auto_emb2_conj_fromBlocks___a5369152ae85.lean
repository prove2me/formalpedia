-- Prove2me | Theorems.Thm_P2M_Auto_emb2_conj_fromBlocks___a5369152ae85
-- name    : P2M_Auto_emb2_conj_fromBlocks___a5369152ae85
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:28.121672+00:00
-- url     : https://prove2.me/theorems/f17accc8-6f5d-4d97-a6a3-86ef6dce97a1
-- title:
--   P2 M Auto emb2 conj from Blocks   a5369152ae85: P2 M Auto emb2 conj from Blocks   a5369152ae85
-- statement:
--   The P2 M Auto emb2 conj from Blocks   a5369152ae85 construction uses the P2 M Auto emb2 conj from Blocks   a5369152ae85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2447-L2454
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2447-L2454

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
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_Auto_emb2_conj_fromBlocks___a5369152ae85 (X11 X12 X21 X22 : Matrix ι ι ℂ) :
    emb2 (ι := ι) 2 0 * Matrix.fromBlocks X11 X12 X21 X22 * (emb2 (ι := ι) 2 0)ᴴ =
      blk3 !![X22, 0, X21; 0, 0, 0; X12, 0, X11] := by sorry

alias «Auto».«emb2_conj_fromBlocks₂₀» := P2M_Auto_emb2_conj_fromBlocks___a5369152ae85
