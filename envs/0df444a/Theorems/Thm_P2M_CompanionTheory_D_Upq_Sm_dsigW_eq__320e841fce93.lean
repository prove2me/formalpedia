-- Prove2me | Theorems.Thm_P2M_CompanionTheory_D_Upq_Sm_dsigW_eq__320e841fce93
-- name    : P2M_CompanionTheory_D_Upq_Sm_dsigW_eq__320e841fce93
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:49:07.308567+00:00
-- url     : https://prove2.me/theorems/6322e2cb-408d-452f-8076-a6c2f0754172
-- title:
--   P2 M Companion Theory D Upq Sm dsig W eq  320e841fce93: P2 M Companion Theory D Upq Sm dsig W eq  320e841fce93
-- statement:
--   The P2 M Companion Theory D Upq Sm dsig W eq  320e841fce93 construction uses the P2 M Companion Theory D Upq Sm dsig W eq  320e841fce93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothCyc.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothCyc.lean#L16-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI.UpqRep

theorem P2M_CompanionTheory_D_Upq_Sm_dsigW_eq__320e841fce93 {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)) :
    ∀ (W : List (Mat (2 * r + k + 1))) (v : H), dsigW (k := k) (r := r) σ W v = dsW σ W v
  := by sorry

alias «CompanionTheory».«D».«Upq».«Sm».«dsigW_eq'» := P2M_CompanionTheory_D_Upq_Sm_dsigW_eq__320e841fce93
