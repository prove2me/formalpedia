-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__det_blockOne_eq_mul_03c1cf12390f
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__det_blockOne_eq_mul_03c1cf12390f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:03:58.282355+00:00
-- url     : https://prove2.me/theorems/371c3181-0ca9-48b4-a39c-6e8c70f9104a
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  det block One eq mul 03c1cf12390f: P2 M Global Theory Companion Theory SW Pi Localization  det block One eq mul 03c1cf12390f
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  det block One eq mul 03c1cf12390f construction uses the P2 M Global Theory Companion Theory SW Pi Localization  det block One eq mul 03c1cf12390f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneScalarPreservesNondegenerate.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneScalarPreservesNondegenerate.lean#L9-L16

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__det_blockOne_eq_mul_03c1cf12390f {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«det_blockOne_eq_mul» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__det_blockOne_eq_mul_03c1cf12390f
