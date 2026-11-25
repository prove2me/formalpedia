-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_det_stdJ_sq
-- name    : ReciprocityTheory.PGsh.det_stdJ_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:33.053954+00:00
-- url     : https://prove2.me/theorems/1a159877-f3e2-4ae6-a82c-d6cdd81267bb
-- title:
--   PGsh: det std J sq
-- statement:
--   The PGsh construction uses the det std J sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAUses.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAUses.lean#L17-L20

import Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAUses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {D : Type} [CommRing D] {g : ℕ}

theorem ReciprocityTheory.PGsh.det_stdJ_sq : (stdJ D g).det ^ 2 = 1 := by sorry
