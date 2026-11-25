-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_det_eq_corner_mul_012aaa08b2f5
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_det_eq_corner_mul_012aaa08b2f5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:03.859825+00:00
-- url     : https://prove2.me/theorems/da48d133-83d0-4e8f-8b90-74556c117969
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit det eq corner mul 012aaa08b2f5: P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit det eq corner mul 012aaa08b2f5
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit det eq corner mul 012aaa08b2f5 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit det eq corner mul 012aaa08b2f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductInvariance.lean#L10-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductInvariance.lean#L10-L38

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductInvariance
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_det_eq_corner_mul_012aaa08b2f5 {K : Type} [CommRing K] {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (w : K) (hw : S 0 0 * w = 1) :
    S.det = S 0 0 *
      (Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ).det := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«BsetUnit».«det_eq_corner_mul» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_det_eq_corner_mul_012aaa08b2f5
