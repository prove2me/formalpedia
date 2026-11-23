-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_apply
-- name    : PI.VolSemiDirect.W.PG.Dat.pU_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:38.765461+00:00
-- url     : https://prove2.me/theorems/7bc542a3-c43e-498e-ab47-0938253ee755
-- title:
--   Dat: p U apply
-- statement:
--   The Dat construction uses the p U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L122-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L122-L122

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

theorem PI.VolSemiDirect.W.PG.Dat.pU_apply (v : n → A) : D.pU v = D.pX v + D.pXv v + D.pz v := by sorry
