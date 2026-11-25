-- Prove2me | Theorems.Thm_PI_VolStabS_FiniteFieldSplitting_ffH_fst
-- name    : PI.VolStabS.FiniteFieldSplitting.ffH_fst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:22.296318+00:00
-- url     : https://prove2.me/theorems/9d3f6d55-94b3-5ab3-854e-f42e94f53f41
-- title:
--   Finite Field Splitting: ff H fst
-- statement:
--   The Finite Field Splitting construction uses the ff H fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFS.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFS.lean#L127-L130

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
variable {k : Type} [Field k] [Finite k] {M a : ℕ}

theorem PI.VolStabS.FiniteFieldSplitting.ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by sorry
