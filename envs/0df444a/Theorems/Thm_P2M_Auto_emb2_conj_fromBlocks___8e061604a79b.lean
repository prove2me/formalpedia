-- Prove2me | Theorems.Thm_P2M_Auto_emb2_conj_fromBlocks___8e061604a79b
-- name    : P2M_Auto_emb2_conj_fromBlocks___8e061604a79b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:18.832289+00:00
-- url     : https://prove2.me/theorems/5b7460d7-0964-4d4c-abb3-b5eec3c2d23f
-- title:
--   P2 M Auto emb2 conj from Blocks   8e061604a79b: P2 M Auto emb2 conj from Blocks   8e061604a79b
-- statement:
--   The P2 M Auto emb2 conj from Blocks   8e061604a79b construction uses the P2 M Auto emb2 conj from Blocks   8e061604a79b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2438-L2445
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2438-L2445

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

theorem P2M_Auto_emb2_conj_fromBlocks___8e061604a79b (X11 X12 X21 X22 : Matrix ι ι ℂ) :
    emb2 (ι := ι) 1 2 * Matrix.fromBlocks X11 X12 X21 X22 * (emb2 (ι := ι) 1 2)ᴴ =
      blk3 !![0, 0, 0; 0, X11, X12; 0, X21, X22] := by sorry

alias «Auto».«emb2_conj_fromBlocks₁₂» := P2M_Auto_emb2_conj_fromBlocks___8e061604a79b
