-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_uni
-- name    : PI.VolSemiDirect.W.PG.Dat.Pi_uni
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:31.201936+00:00
-- url     : https://prove2.me/theorems/8da2d2e8-0ae4-5435-a24e-60561b5638f1
-- title:
--   Dat: Pi uni
-- statement:
--   The Dat construction uses the Pi uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L106-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L106-L121

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
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

theorem PI.VolSemiDirect.W.PG.Dat.Pi_uni (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) :
    D.Uni (D.Pi S) := by sorry
