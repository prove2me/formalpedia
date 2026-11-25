-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_stdJ_mul_self
-- name    : ReciprocityTheory.PGsh.stdJ_mul_self
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:05.399064+00:00
-- url     : https://prove2.me/theorems/8561d022-f079-5312-964a-9379c38ec3f7
-- title:
--   PGsh: std J mul self
-- statement:
--   The PGsh construction uses the std J mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAUses.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAUses.lean#L14-L15

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

theorem ReciprocityTheory.PGsh.stdJ_mul_self : stdJ D g * stdJ D g = -1 := by sorry
