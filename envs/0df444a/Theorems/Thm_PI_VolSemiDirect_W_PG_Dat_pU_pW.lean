-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_pW
-- name    : PI.VolSemiDirect.W.PG.Dat.pU_pW
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:03.694975+00:00
-- url     : https://prove2.me/theorems/668548c6-aba6-4937-9abc-5ba31faee404
-- title:
--   Dat: p U p W
-- statement:
--   The Dat construction uses the p U p W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L162-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L162-L162

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
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
variable (D : Dat A n r)
variable {D}
variable (D)
variable {D}

theorem PI.VolSemiDirect.W.PG.Dat.pU_pW (H : D.Hyp) (v : n → A) : D.pU (D.pW v) = 0 := by sorry
