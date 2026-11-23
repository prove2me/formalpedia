-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_smul_left
-- name    : PI.VolSemiDirect.W.PG.Dat.h_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:29.706894+00:00
-- url     : https://prove2.me/theorems/192a69a8-3d4e-48b8-a7a3-aa3461336f97
-- title:
--   Dat: h smul left
-- statement:
--   The Dat construction uses the h smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L55-L57

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

theorem PI.VolSemiDirect.W.PG.Dat.h_smul_left (x y : n → A) (c : A) : D.h (c • x) y = D.σA c * D.h x y := by sorry
