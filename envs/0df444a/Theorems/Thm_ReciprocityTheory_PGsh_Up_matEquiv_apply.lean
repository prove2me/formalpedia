-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_matEquiv_apply
-- name    : ReciprocityTheory.PGsh.Up.matEquiv_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:51.665812+00:00
-- url     : https://prove2.me/theorems/0137c52d-5f98-4940-8ada-87d5037d68da
-- title:
--   Up: mat Equiv apply
-- statement:
--   The Up construction uses the mat Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MatEquivApply.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MatEquivApply.lean#L18-L21

import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
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
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.PGsh.Up.matEquiv_apply {d : ℕ} (P : Matrix (Fin d) (Fin d) R) (hP : IsUnit P.det) (x : Fin d → R) :
    matEquiv P hP x = P *ᵥ x := by sorry
