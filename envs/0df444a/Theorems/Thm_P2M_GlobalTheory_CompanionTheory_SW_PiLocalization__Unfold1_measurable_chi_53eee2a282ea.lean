-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_chi_53eee2a282ea
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_chi_53eee2a282ea
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:37.913707+00:00
-- url     : https://prove2.me/theorems/c0deedd5-c2fc-40d6-821c-429b45201788
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable chi 53eee2a282ea: P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable chi 53eee2a282ea
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable chi 53eee2a282ea construction uses the P2 M Global Theory Companion Theory SW Pi Localization  Unfold1 measurable chi 53eee2a282ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUnfold.lean#L101-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductUnfold.lean#L101-L127

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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_chi_53eee2a282ea (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    {φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (chi σ J t s a b lam φ) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«Unfold1».«measurable_chi» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold1_measurable_chi_53eee2a282ea
