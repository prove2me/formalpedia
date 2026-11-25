-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_of_span
-- name    : PI.VolSemiDirect.W.PG.Dat.pX_of_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:07.191095+00:00
-- url     : https://prove2.me/theorems/988982d6-1407-5314-8d6a-69437e7dce0e
-- title:
--   Dat: p X of span
-- statement:
--   The Dat construction uses the p X of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModVec.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModVec.lean#L32-L41

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

theorem PI.VolSemiDirect.W.PG.Dat.pX_of_span (H : D.Hyp) {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) :
    D.pX x = x := by sorry
