-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_castSnd_addFst
-- name    : ReciprocityTheory.PGsh.BX.castSnd_addFst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:16.314842+00:00
-- url     : https://prove2.me/theorems/8bdcdd4c-bdbf-40c3-896f-ca260292b0d2
-- title:
--   BX: cast Snd add Fst
-- statement:
--   The BX construction uses the cast Snd add Fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L47-L50

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}

theorem ReciprocityTheory.PGsh.BX.castSnd_addFst {x x' y y' : B.G R} (h : y = y') (u : B.P R x y) (u' : B.P R x' y) :
    B.tr2 h (B.add1 u u') = B.add1 (B.tr2 h u) (B.tr2 h u') := by sorry
