-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__schur_coe_f974b9be1078
-- name    : P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__schur_coe_f974b9be1078
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:12.470128+00:00
-- url     : https://prove2.me/theorems/d1082b55-2ba5-4aa1-807f-8da684687e4a
-- title:
--   P2 M Global Theory Companion Theory SW Pi Localization  schur coe f974b9be1078: P2 M Global Theory Companion Theory SW Pi Localization  schur coe f974b9be1078
-- statement:
--   The P2 M Global Theory Companion Theory SW Pi Localization  schur coe f974b9be1078 construction uses the P2 M Global Theory Companion Theory SW Pi Localization  schur coe f974b9be1078 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/StageData.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/StageData.lean#L39-L42

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__schur_coe_f974b9be1078 (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1))
    (h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n) :
    (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = schurM R σ t a S := by sorry

alias «GlobalTheory».«CompanionTheory».«SW».«PiLocalization₂».«schur_coe» := P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__schur_coe_f974b9be1078
