-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_sat_of_linear
-- name    : PI.IsoDetW.Loc.sat_of_linear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:23.924413+00:00
-- url     : https://prove2.me/theorems/92f6afc3-a3db-4fc6-b12c-bd6c57f5f7be
-- title:
--   Loc: sat of linear
-- statement:
--   The Loc construction uses the sat of linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L178-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LidxAntisymm.lean#L178-L188

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
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
open PI.IsoDetDefs
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K]
variable {W W' : Type*} [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
  [AddCommGroup W'] [Module K W'] [Module R W'] [IsScalarTower R K W']

theorem PI.IsoDetW.Loc.sat_of_linear (p : Ideal R) [p.IsPrime] (f : W →ₗ[K] W') (s : R) (y : W')
    (hs : s ∈ p.primeCompl) (hy : s • y ∈ LinearMap.range (f.restrictScalars R)) :
    y ∈ LinearMap.range (f.restrictScalars R) := by sorry
