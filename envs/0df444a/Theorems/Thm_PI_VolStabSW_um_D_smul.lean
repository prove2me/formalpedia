-- Prove2me | Theorems.Thm_PI_VolStabSW_um_D_smul
-- name    : PI.VolStabSW.um_D_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:18.172803+00:00
-- url     : https://prove2.me/theorems/04aa44d9-a000-5913-9049-a54e11fb5124
-- title:
--   Vol Stab SW: um D smul
-- statement:
--   The Vol Stab SW construction uses the um D smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/Unimod.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/Unimod.lean#L59-L70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_Unimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem PI.VolStabSW.um_D_smul (Γ H : Subgroup G) (x : G) (γ : Γ) : γ • umD Γ H x = umD Γ H x := by sorry
