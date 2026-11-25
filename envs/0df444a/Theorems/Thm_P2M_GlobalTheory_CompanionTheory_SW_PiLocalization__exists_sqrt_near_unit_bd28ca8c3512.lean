-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__exists_sqrt_near_unit_bd28ca8c3512
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__exists_sqrt_near_unit_bd28ca8c3512
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:03.924162+00:00
-- url     : https://prove2.me/theorems/11f0d8ea-d427-4f68-a22d-0601da6234ba
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  exists sqrt near unit bd28ca8c3512: P2 M Global Theory Companion Theory SW Pi Localization  exists sqrt near unit bd28ca8c3512
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  exists sqrt near unit bd28ca8c3512 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  exists sqrt near unit bd28ca8c3512 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalUnitsContinuousSquareRoot.lean#L11-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalUnitsContinuousSquareRoot.lean#L11-L48

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalUnitsContinuousSquareRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__exists_sqrt_near_unit_bd28ca8c3512 : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ,
    ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧
      (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«exists_sqrt_near_unit» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__exists_sqrt_near_unit_bd28ca8c3512
