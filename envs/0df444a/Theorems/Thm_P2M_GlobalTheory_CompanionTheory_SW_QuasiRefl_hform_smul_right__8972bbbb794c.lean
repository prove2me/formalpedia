-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_QuasiRefl_hform_smul_right__8972bbbb794c
-- name    : P2M_GlobalTheory_CompanionTheory_SW_QuasiRefl_hform_smul_right__8972bbbb794c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:30.822153+00:00
-- url     : https://prove2.me/theorems/b262c21d-995d-4802-bfe8-281e06d4f81a
-- title:
--   P2 M Global Theory Companion Theory SW Quasi Refl hform smul right  8972bbbb794c: P2 M Global Theory Companion Theory SW Quasi Refl hform smul right  8972bbbb794c
-- statement:
--   The P2 M Global Theory Companion Theory SW Quasi Refl hform smul right  8972bbbb794c construction uses the P2 M Global Theory Companion Theory SW Quasi Refl hform smul right  8972bbbb794c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GermConstantsEqAlongAffineSpaceSquare.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GermConstantsEqAlongAffineSpaceSquare.lean#L38-L40

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuasiRefl
open HeckeCharacterZeroLocus.SiegelWeilU
variable {A : Type} [CommRing A] {n : Type} [Fintype n] {σ : A →+* A} {J : Matrix n n A}

theorem P2M_GlobalTheory_CompanionTheory_SW_QuasiRefl_hform_smul_right__8972bbbb794c (d y : n → A) (c : A) :
    hform σ J y (c • d) = c * hform σ J y d := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«QuasiRefl».«hform_smul_right'» := P2M_GlobalTheory_CompanionTheory_SW_QuasiRefl_hform_smul_right__8972bbbb794c
