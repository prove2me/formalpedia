-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_actW_vec_zero_858ab6048d78
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_actW_vec_zero_858ab6048d78
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:35.211673+00:00
-- url     : https://prove2.me/theorems/016a23d9-6fb3-4735-9027-29b45f1b34f1
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Cont Two act W vec zero 858ab6048d78: P2 M Global Theory Companion Theory SW Pi Localization  Cont Two act W vec zero 858ab6048d78
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Cont Two act W vec zero 858ab6048d78 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Cont Two act W vec zero 858ab6048d78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L48-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUniqueness.lean#L48-L58

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermFormPulledBackCombinationsExpandMonomials
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_actW_vec_zero_858ab6048d78 {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {N n : ℕ}
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (J' : Matrix (Fin (N + 1)) (Fin (N + 1)) E)
    (h : HA R σ J') (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E) (X : Fin n → Fin N → R ⊗[F] E) (i : Fin (N + 1)) :
    actW R σ J' h (vec A c X) 0 i =
      actW R σ J' h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) 0 i * A := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«ContTwo».«actW_vec_zero» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_actW_vec_zero_858ab6048d78
