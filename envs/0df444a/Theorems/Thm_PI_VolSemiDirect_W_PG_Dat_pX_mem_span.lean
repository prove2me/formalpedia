-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_mem_span
-- name    : PI.VolSemiDirect.W.PG.Dat.pX_mem_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:08.894237+00:00
-- url     : https://prove2.me/theorems/a03a1f8f-d2e9-49e8-8f85-c5d07e499f60
-- title:
--   Dat: p X mem span
-- statement:
--   The Dat construction uses the p X mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean#L154-L156

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

theorem PI.VolSemiDirect.W.PG.Dat.pX_mem_span (u : n → A) : D.pX u ∈ Submodule.span A (Set.range D.e) := by sorry
