-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_half_trace_tmul_6dbb14eaff81
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_half_trace_tmul_6dbb14eaff81
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:59.551195+00:00
-- url     : https://prove2.me/theorems/4588c1b8-c59d-40ec-b1c2-fa37856bdb86
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit half trace tmul 6dbb14eaff81: P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit half trace tmul 6dbb14eaff81
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit half trace tmul 6dbb14eaff81 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit half trace tmul 6dbb14eaff81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductInvariance.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductInvariance.lean#L42-L50

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_half_trace_tmul_6dbb14eaff81 (h2F : (2 : F) ≠ 0) (b : Module.Basis (Fin 2) F E) (r : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«BsetUnit».«half_trace_tmul» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_half_trace_tmul_6dbb14eaff81
