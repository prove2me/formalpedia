-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_castSnd_eq_iff
-- name    : ReciprocityTheory.PGsh.BX.castSnd_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:57.022302+00:00
-- url     : https://prove2.me/theorems/b2643d7f-64db-4c31-ab3c-38976ce40d91
-- title:
--   BX: cast Snd eq iff
-- statement:
--   The BX construction uses the cast Snd eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L27-L35

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

theorem ReciprocityTheory.PGsh.BX.castSnd_eq_iff {a b x : B.G R} (h : a = b) (u : B.P R x a) (w : B.P R x b) :
    B.tr2 h u = w ↔ (⟨a, u⟩ : B.S2 R x) = ⟨b, w⟩ := by sorry
