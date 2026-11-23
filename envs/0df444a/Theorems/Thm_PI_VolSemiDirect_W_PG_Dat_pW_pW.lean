-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_pW
-- name    : PI.VolSemiDirect.W.PG.Dat.pW_pW
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:35.798538+00:00
-- url     : https://prove2.me/theorems/fbbdcada-e552-498f-b227-62b9ce08dca3
-- title:
--   Dat: p W p W
-- statement:
--   The Dat construction uses the p W p W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L164-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjGen.lean#L164-L164

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

theorem PI.VolSemiDirect.W.PG.Dat.pW_pW (H : D.Hyp) (v : n → A) : D.pW (D.pW v) = D.pW v := by sorry
