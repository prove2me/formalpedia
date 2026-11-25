-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_emb_le_one_iff
-- name    : PI.VolStabSW.FiniteThetaCoordinates.norm_emb_le_one_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:39:20.830203+00:00
-- url     : https://prove2.me/theorems/27b0bee2-cb8d-5d89-9c3c-1d9f08273d9c
-- title:
--   Finite Theta Coordinates: norm emb le one iff
-- statement:
--   The Finite Theta Coordinates construction uses the norm emb le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L177-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L177-L180

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

theorem PI.VolStabSW.FiniteThetaCoordinates.norm_emb_le_one_iff (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖FinitePlace.embedding v x‖ ≤ 1 ↔ v.valuation F x ≤ 1 := by sorry
