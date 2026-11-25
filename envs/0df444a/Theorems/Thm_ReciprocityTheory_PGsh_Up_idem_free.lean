-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_idem_free
-- name    : ReciprocityTheory.PGsh.Up.idem_free
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:10:18.513938+00:00
-- url     : https://prove2.me/theorems/3a96b325-fe74-47cb-a285-b6b8ec73c3eb
-- title:
--   Up: idem free
-- statement:
--   The Up construction uses the idem free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InvolutionPermApplyZero.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/InvolutionPermApplyZero.lean#L13-L35

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonOf
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm
import Definitions.Def_ReciprocityTheory_DualLattices_InvolutionPermApplyZero
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
open ReciprocityTheory.PGsh.L2

theorem ReciprocityTheory.PGsh.Up.idem_free {R : Type} [CommRing R] [IsLocalRing R] {g : ℕ} (P : Matrix (Fin g) (Fin g) R)
    (hP : P * P = P) : ∃ d : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R)) := by sorry
