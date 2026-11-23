-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_hasLen_coker_det__d6b912bda411
-- name    : P2M_ReciprocityTheory_PGsh_Up_hasLen_coker_det__d6b912bda411
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:02.21769+00:00
-- url     : https://prove2.me/theorems/00f265db-ac3e-4ae1-a42e-32a2a3427de5
-- title:
--   P2 M Reciprocity Theory PGsh Up has Len coker det  d6b912bda411: P2 M Reciprocity Theory PGsh Up has Len coker det  d6b912bda411
-- statement:
--   The P2 M Reciprocity Theory PGsh Up has Len coker det  d6b912bda411 construction uses the P2 M Reciprocity Theory PGsh Up has Len coker det  d6b912bda411 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HasLenCokerDet.lean#L16-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HasLenCokerDet.lean#L16-L41

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up

theorem P2M_ReciprocityTheory_PGsh_Up_hasLen_coker_det__d6b912bda411 {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R) :
    HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)) := by sorry

alias «ReciprocityTheory».«PGsh».«Up».«hasLen_coker_det'» := P2M_ReciprocityTheory_PGsh_Up_hasLen_coker_det__d6b912bda411
