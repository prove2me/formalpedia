-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_measurable_Pint__708cef7c8a2f
-- name    : P2M_GlobalTheory_T_measurable_Pint__708cef7c8a2f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:23.665646+00:00
-- url     : https://prove2.me/theorems/4043cb55-1f0a-4048-a22e-6d6bdec56856
-- title:
--   P2 M Global Theory T measurable Pint  708cef7c8a2f: P2 M Global Theory T measurable Pint  708cef7c8a2f
-- statement:
--   The P2 M Global Theory T measurable Pint  708cef7c8a2f construction uses the P2 M Global Theory T measurable Pint  708cef7c8a2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFubiniStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductFubiniStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFubini
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFubiniStatement
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
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_measurable_Pint__708cef7c8a2f : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by sorry

alias «GlobalTheory».«T».«measurable_Pint'» := P2M_GlobalTheory_T_measurable_Pint__708cef7c8a2f
