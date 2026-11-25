-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_N_eq_L
-- name    : PI.VolSemiDirect.W.PG.Dat.N_eq_L
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:11.089465+00:00
-- url     : https://prove2.me/theorems/843442c6-e03f-5b5c-b581-c848a34f97e5
-- title:
--   Dat: N eq L
-- statement:
--   The Dat construction uses the N eq L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L58-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L58-L105

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

theorem PI.VolSemiDirect.W.PG.Dat.N_eq_L (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S)
    (hP : D.PerpX S) (v : n → A) :
    S v = D.L (fun b => D.pW (S (D.f b))) (fun a b => D.h (D.f a) (S (D.f b))) v := by sorry
