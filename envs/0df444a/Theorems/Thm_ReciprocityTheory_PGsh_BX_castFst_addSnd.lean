-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_addSnd
-- name    : ReciprocityTheory.PGsh.BX.castFst_addSnd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:28.922692+00:00
-- url     : https://prove2.me/theorems/11f5babc-d9b4-4f3b-b812-2b891ae581bb
-- title:
--   BX: cast Fst add Snd
-- statement:
--   The BX construction uses the cast Fst add Snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L52-L55

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

theorem ReciprocityTheory.PGsh.BX.castFst_addSnd {x x' y y' : B.G R} (h : x = x') (u : B.P R x y) (u' : B.P R x y') :
    B.tr1 h (B.add2 u u') = B.add2 (B.tr1 h u) (B.tr1 h u') := by sorry
