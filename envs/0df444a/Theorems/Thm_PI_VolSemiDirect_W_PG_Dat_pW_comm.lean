-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_comm
-- name    : PI.VolSemiDirect.W.PG.Dat.pW_comm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:30.472844+00:00
-- url     : https://prove2.me/theorems/4c8b11cc-a65a-4050-817c-62d48bfa197b
-- title:
--   Dat: p W comm
-- statement:
--   The Dat construction uses the p W comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L144-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L144-L160

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

theorem PI.VolSemiDirect.W.PG.Dat.pW_comm (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S)
    (hf : ∀ a, S (D.f a) = D.f a) (hU : D.Uni S) (v : n → A) : D.pW (S v) = S (D.pW v) := by sorry
