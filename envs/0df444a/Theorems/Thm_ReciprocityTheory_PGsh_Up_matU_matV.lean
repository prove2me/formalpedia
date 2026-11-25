-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_matU_matV
-- name    : ReciprocityTheory.PGsh.Up.matU_matV
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:08.795599+00:00
-- url     : https://prove2.me/theorems/ed816f44-9bb3-4fc0-bd2a-34f41c08c467
-- title:
--   Up: mat U mat V
-- statement:
--   The Up construction uses the mat U mat V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualLenStatement.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DualLenStatement.lean#L81-L87

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

theorem ReciprocityTheory.PGsh.Up.matU_matV : matU P φ * matV P φ = P := by sorry
