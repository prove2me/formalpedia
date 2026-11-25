-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmulFst_addSnd
-- name    : ReciprocityTheory.PGsh.BX.nsmulFst_addSnd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:42.675801+00:00
-- url     : https://prove2.me/theorems/1e016699-7b70-48ac-8acf-718af2fe3171
-- title:
--   BX: nsmul Fst add Snd
-- statement:
--   The BX construction uses the nsmul Fst add Snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulFstAddSnd.lean#L15-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulFstAddSnd.lean#L15-L34

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
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

theorem ReciprocityTheory.PGsh.BX.nsmulFst_addSnd {x y y' : B.G R} (u : B.P R x y) (u' : B.P R x y') (n : ℕ) :
    B.nsmul1 (B.add2 u u') n = B.add2 (B.nsmul1 u n) (B.nsmul1 u' n) := by sorry
