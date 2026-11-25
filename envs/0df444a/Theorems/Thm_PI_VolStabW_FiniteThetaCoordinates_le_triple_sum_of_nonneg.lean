-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_le_triple_sum_of_nonneg
-- name    : PI.VolStabW.FiniteThetaCoordinates.le_triple_sum_of_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:44:09.795451+00:00
-- url     : https://prove2.me/theorems/ded84c2a-5a5c-4948-979b-9e7ba289346f
-- title:
--   Finite Theta Coordinates: le triple sum of nonneg
-- statement:
--   The Finite Theta Coordinates construction uses the le triple sum of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L244-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L244-L254

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

theorem PI.VolStabW.FiniteThetaCoordinates.le_triple_sum_of_nonneg {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν] (f : ι → κ → ν → ℝ)
    (hf : ∀ i j k, 0 ≤ f i j k) (i : ι) (j : κ) (k : ν) : f i j k ≤ ∑ i, ∑ j, ∑ k, f i j k := by sorry
