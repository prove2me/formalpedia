-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_right__dc8b27524d6b
-- name    : P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_right__dc8b27524d6b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:35.976475+00:00
-- url     : https://prove2.me/theorems/378a9904-51ef-4c53-807a-bba266ecb94d
-- title:
--   P2 M Global Theory Companion Theory SW Unit Rep hform smul right  dc8b27524d6b: P2 M Global Theory Companion Theory SW Unit Rep hform smul right  dc8b27524d6b
-- statement:
--   The P2 M Global Theory Companion Theory SW Unit Rep hform smul right  dc8b27524d6b construction uses the P2 M Global Theory Companion Theory SW Unit Rep hform smul right  dc8b27524d6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L23-L26

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitRep
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_right__dc8b27524d6b (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J x (a • y) = a * hform σ J x y := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«UnitRep».«hform_smul_right'» := P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_right__dc8b27524d6b
