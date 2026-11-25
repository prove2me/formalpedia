-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_pX_f
-- name    : PI.VolSemiDirect.W.PG.Dat.h_pX_f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:38:32.264588+00:00
-- url     : https://prove2.me/theorems/aaff826d-b990-5e2a-ae5b-f8d015e3f1b7
-- title:
--   Dat: h p X f
-- statement:
--   The Dat construction uses the h p X f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L115-L118

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}

theorem PI.VolSemiDirect.W.PG.Dat.h_pX_f (H : D.Hyp) (b : Fin r) (u : n → A) :
    D.h (D.pX u) (D.f b) = D.σA (D.h (D.f b) u) := by sorry
