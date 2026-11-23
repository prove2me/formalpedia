-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_smul_algebraMap
-- name    : PI.IsoDetW.Loc.smul_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:09.08516+00:00
-- url     : https://prove2.me/theorems/0b550d99-ba3b-4fbc-a43b-580eccc8c055
-- title:
--   Loc: smul algebra Map
-- statement:
--   The Loc construction uses the smul algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/AlgebraMapMemCI.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/AlgebraMapMemCI.lean#L46-L47

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

theorem PI.IsoDetW.Loc.smul_algebraMap (s y : R) : s • algebraMap R K y = algebraMap R K (s * y) := by sorry
