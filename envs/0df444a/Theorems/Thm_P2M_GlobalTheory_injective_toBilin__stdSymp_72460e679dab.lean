-- Prove2me | Theorems.Thm_P2M_GlobalTheory_injective_toBilin__stdSymp_72460e679dab
-- name    : P2M_GlobalTheory_injective_toBilin__stdSymp_72460e679dab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:05.138802+00:00
-- url     : https://prove2.me/theorems/fed6db72-2ab8-46c7-a676-28a85fa0007d
-- title:
--   P2 M Global Theory injective to Bilin  std Symp 72460e679dab: P2 M Global Theory injective to Bilin  std Symp 72460e679dab
-- statement:
--   The P2 M Global Theory injective to Bilin  std Symp 72460e679dab construction uses the P2 M Global Theory injective to Bilin  std Symp 72460e679dab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L128-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsNeZeroHalfStandardAltFormConstOfExponentOn.lean#L128-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsNeZeroHalfStandardAltFormConstOfExponentOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Out

theorem P2M_GlobalTheory_injective_toBilin__stdSymp_72460e679dab {R : Type*} [CommRing R] (g : ℕ) :
    Injective (Matrix.toBilin' (Matrix.of fun i j => ((stdSymp g i j : ℤ) : R))) := by sorry

alias «GlobalTheory».«injective_toBilin'_stdSymp» := P2M_GlobalTheory_injective_toBilin__stdSymp_72460e679dab
