-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_isUnit_det_of_mem_Bset_709514adee71
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_isUnit_det_of_mem_Bset_709514adee71
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:25.489942+00:00
-- url     : https://prove2.me/theorems/4f614f2f-50a5-4fca-9022-f92f5f484b77
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit is Unit det of mem Bset 709514adee71: P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit is Unit det of mem Bset 709514
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit is Unit det of mem Bset 709514adee71 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Bset Unit is Unit det of mem Bset 709514adee71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductInvariance.lean#L70-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductInvariance.lean#L70-L119

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_isUnit_det_of_mem_Bset_709514adee71 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«BsetUnit».«isUnit_det_of_mem_Bset» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__BsetUnit_isUnit_det_of_mem_Bset_709514adee71
