-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_swap_castSnd
-- name    : ReciprocityTheory.PGsh.BX.swap_castSnd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:45.625247+00:00
-- url     : https://prove2.me/theorems/2518c261-7d32-421f-a75e-25a1aa88a7f3
-- title:
--   BX: swap cast Snd
-- statement:
--   The BX construction uses the swap cast Snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L57-L60

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

theorem ReciprocityTheory.PGsh.BX.swap_castSnd {x y y' : B.G R} (h : y = y') (u : B.P R x y) :
    B.sw (B.tr2 h u) = B.tr1 h (B.sw u) := by sorry
