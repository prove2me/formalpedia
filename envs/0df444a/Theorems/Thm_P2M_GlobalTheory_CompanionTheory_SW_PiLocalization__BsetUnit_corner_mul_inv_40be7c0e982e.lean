-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_corner_mul_inv_40be7c0e982e
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_corner_mul_inv_40be7c0e982e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:02.850504+00:00
-- url     : https://prove2.me/theorems/bf297e56-1e0a-48de-beb8-fe9902034917
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit corner mul inv 40be7c0e982e: P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit corner mul inv 40be7c0e982e
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit corner mul inv 40be7c0e982e construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit corner mul inv 40be7c0e982e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductInvariance.lean#L52-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductInvariance.lean#L52-L68

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_corner_mul_inv_40be7c0e982e {t : F} (ht : t ≠ 0) (u : Rˣ) :
    (((u : R) ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E)) *
      ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * inclR R (algebraMap F E t) *
        (((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) = 1 := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«BsetUnit».«corner_mul_inv» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_corner_mul_inv_40be7c0e982e
