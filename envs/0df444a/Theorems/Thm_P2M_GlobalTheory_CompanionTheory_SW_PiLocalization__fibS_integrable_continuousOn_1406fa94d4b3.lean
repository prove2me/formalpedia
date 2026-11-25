-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__fibS_integrable_continuousOn_1406fa94d4b3
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__fibS_integrable_continuousOn_1406fa94d4b3
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:50.138812+00:00
-- url     : https://prove2.me/theorems/bf94527c-77c9-4d67-b9ce-8b1c3edd3087
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  fib S integrable continuous On 1406fa94d4b3: P2 M Global Theory Companion Theory SW Pi Localization  fib S integrable continuous On 1406fa94d4b3
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  fib S integrable continuous On 1406fa94d4b3 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  fib S integrable continuous On 1406fa94d4b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductRecursion.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductRecursion.lean#L10-L24

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductScalingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUniquenessStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegralStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductRecursion
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

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__fibS_integrable_continuousOn_1406fa94d4b3 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S)) ∧ ContinuousOn (fun S => ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)) (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«fibS_integrable_continuousOn» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__fibS_integrable_continuousOn_1406fa94d4b3
