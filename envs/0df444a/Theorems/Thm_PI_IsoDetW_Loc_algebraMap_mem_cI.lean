-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_algebraMap_mem_cI
-- name    : PI.IsoDetW.Loc.algebraMap_mem_cI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:46.590557+00:00
-- url     : https://prove2.me/theorems/9c5293ee-7af3-422a-9d9b-b4f6d46475ab
-- title:
--   Loc: algebra Map mem c I
-- statement:
--   The Loc construction uses the algebra Map mem c I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/AlgebraMapMemCI.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/AlgebraMapMemCI.lean#L39-L44

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

theorem PI.IsoDetW.Loc.algebraMap_mem_cI {J : Ideal R} {y : R} : algebraMap R K y ∈ cI K J ↔ y ∈ J := by sorry
