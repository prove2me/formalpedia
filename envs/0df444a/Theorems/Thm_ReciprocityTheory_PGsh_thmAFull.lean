-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_thmAFull
-- name    : ReciprocityTheory.PGsh.thmAFull
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:44.624897+00:00
-- url     : https://prove2.me/theorems/b744b8f2-2d16-5f8d-b2c8-da9a7571c255
-- title:
--   PGsh: thm AFull
-- statement:
--   The PGsh construction uses the thm AFull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAFull.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAFull.lean#L38-L49

import Definitions.Def_ReciprocityTheory_DualLattices_OneAddPowOfSq
import Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAFull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Matrix
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R₀ : Type} [CommRing R₀]

theorem ReciprocityTheory.PGsh.thmAFull (B : BX R₀) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) {p : ℕ}
    (Tw : ATower R₀ p) : ThmAFullStatement B Tw := by sorry
