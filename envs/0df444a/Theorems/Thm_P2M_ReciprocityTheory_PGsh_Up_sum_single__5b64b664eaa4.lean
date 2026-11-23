-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_sum_single__5b64b664eaa4
-- name    : P2M_ReciprocityTheory_PGsh_Up_sum_single__5b64b664eaa4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:15.283804+00:00
-- url     : https://prove2.me/theorems/842f48bb-3158-4b77-b937-276b2aaa7ab8
-- title:
--   P2 M Reciprocity Theory PGsh Up sum single  5b64b664eaa4: P2 M Reciprocity Theory PGsh Up sum single  5b64b664eaa4
-- statement:
--   The P2 M Reciprocity Theory PGsh Up sum single  5b64b664eaa4 construction uses the P2 M Reciprocity Theory PGsh Up sum single  5b64b664eaa4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualLenStatement.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualLenStatement.lean#L38-L40

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
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
variable {R : Type} [CommRing R] {g d : ℕ} (P : Matrix (Fin g) (Fin g) R) (hP : P * P = P)
  (φ : LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R))

theorem P2M_ReciprocityTheory_PGsh_Up_sum_single__5b64b664eaa4 {n : ℕ} (y : Fin n → R) : y = ∑ l, y l • (Pi.single l 1 : Fin n → R) := by sorry

alias «ReciprocityTheory».«PGsh».«Up».«sum_single'» := P2M_ReciprocityTheory_PGsh_Up_sum_single__5b64b664eaa4
