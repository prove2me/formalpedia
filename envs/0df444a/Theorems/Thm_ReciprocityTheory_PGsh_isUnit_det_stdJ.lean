-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_isUnit_det_stdJ
-- name    : ReciprocityTheory.PGsh.isUnit_det_stdJ
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:48.605414+00:00
-- url     : https://prove2.me/theorems/95f13bee-cb44-4723-831c-71e746c7449a
-- title:
--   PGsh: is Unit det std J
-- statement:
--   The PGsh construction uses the is Unit det std J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAUses.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAUses.lean#L22-L23

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

theorem ReciprocityTheory.PGsh.isUnit_det_stdJ : IsUnit (stdJ D g).det := by sorry
