-- Prove2me | Theorems.Thm_P2M_PI_VolSemiDirect_W_PG_Dat_N_f__c785d52daa49
-- name    : P2M_PI_VolSemiDirect_W_PG_Dat_N_f__c785d52daa49
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:01:22.034433+00:00
-- url     : https://prove2.me/theorems/9bd5d0d3-8d8b-46e6-8612-da593ccdb396
-- title:
--   P2 M PI Vol Semi Direct W PG Dat N f  c785d52daa49: P2 M PI Vol Semi Direct W PG Dat N f  c785d52daa49
-- statement:
--   The P2 M PI Vol Semi Direct W PG Dat N f  c785d52daa49 construction uses the P2 M PI Vol Semi Direct W PG Dat N f  c785d52daa49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ReflectionFixesNormal.lean#L124-L127

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

theorem P2M_PI_VolSemiDirect_W_PG_Dat_N_f__c785d52daa49 (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (b : Fin r) :
    S (D.f b) = D.f b + D.pW (S (D.f b)) + D.pX (S (D.f b)) := by sorry

alias «PI».«VolSemiDirect».«W».«PG».«Dat».«N_f'» := P2M_PI_VolSemiDirect_W_PG_Dat_N_f__c785d52daa49
