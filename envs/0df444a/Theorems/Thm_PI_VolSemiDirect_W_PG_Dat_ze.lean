-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_ze
-- name    : PI.VolSemiDirect.W.PG.Dat.ze
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:55.508952+00:00
-- url     : https://prove2.me/theorems/e2850061-16a1-425b-8ff5-d3f454ddbff4
-- title:
--   Dat: ze
-- statement:
--   The Dat construction uses the ze property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L93-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L93-L94

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

theorem PI.VolSemiDirect.W.PG.Dat.ze (H : D.Hyp) (a : Fin r) : D.h D.z (D.e a) = 0 := by sorry
