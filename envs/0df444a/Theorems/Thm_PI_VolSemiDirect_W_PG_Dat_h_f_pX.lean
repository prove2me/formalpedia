-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_f_pX
-- name    : PI.VolSemiDirect.W.PG.Dat.h_f_pX
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:37:20.235673+00:00
-- url     : https://prove2.me/theorems/33e00c96-37bf-54fb-9cf3-cbbc97d84dc2
-- title:
--   Dat: h f p X
-- statement:
--   The Dat construction uses the h f p X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L107-L113

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

theorem PI.VolSemiDirect.W.PG.Dat.h_f_pX (H : D.Hyp) (a : Fin r) (u : n → A) : D.h (D.f a) (D.pX u) = D.h (D.f a) u := by sorry
