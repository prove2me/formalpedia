-- Prove2me | Theorems.Thm_PI_VolStabS_FiniteFieldSplitting_card_left_inv
-- name    : PI.VolStabS.FiniteFieldSplitting.card_left_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:16.081143+00:00
-- url     : https://prove2.me/theorems/a80a93d5-eb66-5ee2-93b5-7a44905bf97a
-- title:
--   Finite Field Splitting: card left inv
-- statement:
--   The Finite Field Splitting construction uses the card left inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFS.lean#L59-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFS.lean#L59-L85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]

theorem PI.VolStabS.FiniteFieldSplitting.card_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by sorry
