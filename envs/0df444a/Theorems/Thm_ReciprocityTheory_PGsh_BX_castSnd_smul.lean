-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_castSnd_smul
-- name    : ReciprocityTheory.PGsh.BX.castSnd_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:20.900515+00:00
-- url     : https://prove2.me/theorems/e89cd412-b128-5597-b978-e65bf4c32a7a
-- title:
--   BX: cast Snd smul
-- statement:
--   The BX construction uses the cast Snd smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L42-L45

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

theorem ReciprocityTheory.PGsh.BX.castSnd_smul {a b x : B.G R} (h : a = b) (l : (R : Type u)ˣ) (u : B.P R x a) :
    B.tr2 h (B.smul l u) = B.smul l (B.tr2 h u) := by sorry
