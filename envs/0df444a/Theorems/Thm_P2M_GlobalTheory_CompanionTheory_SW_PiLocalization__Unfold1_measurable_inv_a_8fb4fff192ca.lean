-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_inv_a_8fb4fff192ca
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_inv_a_8fb4fff192ca
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:28.436+00:00
-- url     : https://prove2.me/theorems/1ce72ff6-3043-405d-aaf4-6dd64c858a8e
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable inv a 8fb4fff192ca: P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable inv a 8fb4fff192ca
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable inv a 8fb4fff192ca construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable inv a 8fb4fff192ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUnfold.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUnfold.lean#L70-L82

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureOrthogonalExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegralStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUnfold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {t : F} {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E} {lam : Measure R}
  {m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)}
  {m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)}
  {s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)}
  {B₀ : Set R} {a : R → Rˣ} {κ₁ cm : Rˣ → ℝ≥0}
include R

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_inv_a_8fb4fff192ca (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm) :
    Measurable fun x : R => ((((a x)⁻¹ : Rˣ) : R)) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«Unfold1».«measurable_inv_a» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_inv_a_8fb4fff192ca
