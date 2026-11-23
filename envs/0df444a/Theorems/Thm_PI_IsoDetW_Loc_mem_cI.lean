-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_mem_cI
-- name    : PI.IsoDetW.Loc.mem_cI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:06.440136+00:00
-- url     : https://prove2.me/theorems/da839468-06c6-4bba-9991-cfc96d906fa9
-- title:
--   Loc: mem c I
-- statement:
--   The Loc construction uses the mem c I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/AlgebraMapMemCI.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/AlgebraMapMemCI.lean#L36-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem PI.IsoDetW.Loc.mem_cI {J : Ideal R} {x : K} : x ∈ cI K J ↔ ∃ y ∈ J, algebraMap R K y = x := by sorry
