-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isHermND_blockOne_algebraMap_4c79e73c2c38
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isHermND_blockOne_algebraMap_4c79e73c2c38
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:56.257845+00:00
-- url     : https://prove2.me/theorems/0fef63eb-8313-4b86-90ff-b0b96eb9fe80
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  is Herm ND block One algebra Map 4c79e73c2c38: P2 M Global Theory Companion Theory SW Pi Localization  is Herm ND block One algebra Map 4c79e73c
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  is Herm ND block One algebra Map 4c79e73c2c38 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  is Herm ND block One algebra Map 4c79e73c2c38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneScalarPreservesNondegenerate.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneScalarPreservesNondegenerate.lean#L18-L27

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isHermND_blockOne_algebraMap_4c79e73c2c38 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«isHermND_blockOne_algebraMap» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isHermND_blockOne_algebraMap_4c79e73c2c38
