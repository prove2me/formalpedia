-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_finite_bdd
-- name    : PI.VolStabW.FiniteThetaCoordinates.finite_bdd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:43:32.667165+00:00
-- url     : https://prove2.me/theorems/f70e9053-5cae-4275-9457-2e9b14327dd8
-- title:
--   Finite Theta Coordinates: finite bdd
-- statement:
--   The Finite Theta Coordinates construction uses the finite bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L182-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L182-L238

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
variable {F : Type} [Field F] [NumberField F]

theorem PI.VolStabW.FiniteThetaCoordinates.finite_bdd (S : Finset (HeightOneSpectrum (𝓞 F))) (C : HeightOneSpectrum (𝓞 F) → ℝ)
    (Ci : InfinitePlace F → ℝ) :
    {x : F | (∀ v, ‖FinitePlace.embedding v x‖ ≤ C v) ∧
      (∀ v ∉ S, ‖FinitePlace.embedding v x‖ ≤ 1) ∧ ∀ w : InfinitePlace F, w x ≤ Ci w}.Finite := by sorry
