-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_finite_bdd
-- name    : PI.VolStabSW.FiniteThetaCoordinates.finite_bdd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:39:01.474094+00:00
-- url     : https://prove2.me/theorems/d8668ac7-94df-4ffb-bd94-ed49a2b34f33
-- title:
--   Finite Theta Coordinates: finite bdd
-- statement:
--   The Finite Theta Coordinates construction uses the finite bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L182-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L182-L238

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]

theorem PI.VolStabSW.FiniteThetaCoordinates.finite_bdd (S : Finset (HeightOneSpectrum (𝓞 F))) (C : HeightOneSpectrum (𝓞 F) → ℝ)
    (Ci : InfinitePlace F → ℝ) :
    {x : F | (∀ v, ‖FinitePlace.embedding v x‖ ≤ C v) ∧
      (∀ v ∉ S, ‖FinitePlace.embedding v x‖ ≤ 1) ∧ ∀ w : InfinitePlace F, w x ≤ Ci w}.Finite := by sorry
