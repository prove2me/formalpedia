-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_left__f3e0ebeac993
-- name    : P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_left__f3e0ebeac993
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:23.122637+00:00
-- url     : https://prove2.me/theorems/30a7fc33-38b2-4f19-bbe5-4a56ca1fa759
-- title:
--   P2 M Global Theory Companion Theory SW Unit Rep hform smul left  f3e0ebeac993: P2 M Global Theory Companion Theory SW Unit Rep hform smul left  f3e0ebeac993
-- statement:
--   The P2 M Global Theory Companion Theory SW Unit Rep hform smul left  f3e0ebeac993 construction uses the P2 M Global Theory Companion Theory SW Unit Rep hform smul left  f3e0ebeac993 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L19-L21

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

theorem P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_left__f3e0ebeac993 (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J (a • x) y = σ a * hform σ J x y := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«UnitRep».«hform_smul_left'» := P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_left__f3e0ebeac993
