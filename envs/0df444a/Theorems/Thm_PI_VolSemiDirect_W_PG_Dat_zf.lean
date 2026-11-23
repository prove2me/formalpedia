-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_zf
-- name    : PI.VolSemiDirect.W.PG.Dat.zf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:00.507781+00:00
-- url     : https://prove2.me/theorems/60a10bd0-7dac-4da7-9daf-222eb94330ec
-- title:
--   Dat: zf
-- statement:
--   The Dat construction uses the zf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L96-L97

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

theorem PI.VolSemiDirect.W.PG.Dat.zf (H : D.Hyp) (a : Fin r) : D.h D.z (D.f a) = 0 := by sorry
