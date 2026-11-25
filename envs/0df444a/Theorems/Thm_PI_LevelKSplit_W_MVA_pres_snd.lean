-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_MVA_pres_snd
-- name    : PI.LevelKSplit.W.MVA.pres_snd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:40.006564+00:00
-- url     : https://prove2.me/theorems/afed9e4a-1e0e-4bb3-afbb-26321816c69c
-- title:
--   MVA: pres snd
-- statement:
--   The MVA construction uses the pres snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousFirstOrbitMap.lean#L130-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousFirstOrbitMap.lean#L130-L163

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousFirstOrbitMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [LocallyCompactSpace R1] [T2Space R1]
  [SecondCountableTopology R1]
  [TopologicalSpace R2] [IsTopologicalRing R2] [LocallyCompactSpace R2] [T2Space R2]
  [SecondCountableTopology R2]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem PI.LevelKSplit.W.MVA.pres_snd
    (hV : ∀ (g : HA (R1 × R2) σ J) (ν : Measure (Fin M → (R1 × R2) ⊗[F] E)),
      ν.IsAddHaarMeasure → ν.map (lin (R1 × R2) σ J g) = ν)
    (g : HA R2 σ J) (μ : Measure (Fin M → R2 ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (lin R2 σ J g) = μ := by sorry
