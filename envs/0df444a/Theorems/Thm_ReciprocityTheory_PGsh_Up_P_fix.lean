-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_P_fix
-- name    : ReciprocityTheory.PGsh.Up.P_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:43.84272+00:00
-- url     : https://prove2.me/theorems/383fb6f6-19f2-4154-90b8-878a536b4a5b
-- title:
--   Up: P fix
-- statement:
--   The Up construction uses the P fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualLenStatement.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualLenStatement.lean#L43-L45

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
include hP

theorem ReciprocityTheory.PGsh.Up.P_fix (x : Fin g → R) (hx : x ∈ LinearMap.range (Matrix.mulVecLin P)) : P *ᵥ x = x := by sorry
