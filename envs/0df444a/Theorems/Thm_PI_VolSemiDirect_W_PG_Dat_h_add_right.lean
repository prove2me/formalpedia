-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_right
-- name    : PI.VolSemiDirect.W.PG.Dat.h_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:56.15513+00:00
-- url     : https://prove2.me/theorems/cdaddc81-6eec-4d68-a041-6be73eb53c99
-- title:
--   Dat: h add right
-- statement:
--   The Dat construction uses the h add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L36-L37

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

theorem PI.VolSemiDirect.W.PG.Dat.h_add_right (x y y' : n → A) : D.h x (y + y') = D.h x y + D.h x y' := by sorry
