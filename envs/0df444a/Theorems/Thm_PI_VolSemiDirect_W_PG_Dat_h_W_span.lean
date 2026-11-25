-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_W_span
-- name    : PI.VolSemiDirect.W.PG.Dat.h_W_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:29.562348+00:00
-- url     : https://prove2.me/theorems/91af87ca-a79c-4d32-84da-60a1e1695c54
-- title:
--   Dat: h W span
-- statement:
--   The Dat construction uses the h W span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModVec.lean#L46-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModVec.lean#L46-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
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

theorem PI.VolSemiDirect.W.PG.Dat.h_W_span (H : D.Hyp) {w : n → A} (hw : IsW D w) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : D.h w x = 0 := by sorry
