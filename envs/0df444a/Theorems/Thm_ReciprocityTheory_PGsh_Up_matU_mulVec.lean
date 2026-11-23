-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_matU_mulVec
-- name    : ReciprocityTheory.PGsh.Up.matU_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:14.106005+00:00
-- url     : https://prove2.me/theorems/d0375d5c-0804-4051-8c4d-0063f444ff7a
-- title:
--   Up: mat U mul Vec
-- statement:
--   The Up construction uses the mat U mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualLenStatement.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualLenStatement.lean#L47-L51

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

theorem ReciprocityTheory.PGsh.Up.matU_mulVec (y : Fin d → R) : matU P φ *ᵥ y = (φ.symm y : Fin g → R) := by sorry
