-- Prove2me | Theorems.Thm_P2M_Auto_emb2_conj_fromBlocks___e2a989298a5e
-- name    : P2M_Auto_emb2_conj_fromBlocks___e2a989298a5e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:21.913269+00:00
-- url     : https://prove2.me/theorems/677607d8-e06a-4831-a1ff-925c0141d3dc
-- title:
--   P2 M Auto emb2 conj from Blocks   e2a989298a5e: P2 M Auto emb2 conj from Blocks   e2a989298a5e
-- statement:
--   The P2 M Auto emb2 conj from Blocks   e2a989298a5e construction uses the P2 M Auto emb2 conj from Blocks   e2a989298a5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2456-L2463
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2456-L2463

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

theorem P2M_Auto_emb2_conj_fromBlocks___e2a989298a5e (X11 X12 X21 X22 : Matrix ι ι ℂ) :
    emb2 (ι := ι) 0 1 * Matrix.fromBlocks X11 X12 X21 X22 * (emb2 (ι := ι) 0 1)ᴴ =
      blk3 !![X11, X12, 0; X21, X22, 0; 0, 0, 0] := by sorry

alias «Auto».«emb2_conj_fromBlocks₀₁» := P2M_Auto_emb2_conj_fromBlocks___e2a989298a5e
