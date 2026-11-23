-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_mulR_sat
-- name    : PI.IsoDetW.Loc.mulR_sat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:46.49118+00:00
-- url     : https://prove2.me/theorems/301cb305-67f3-4a5f-8fa8-b08f47b6065f
-- title:
--   Loc: mul R sat
-- statement:
--   The Loc construction uses the mul R sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L19-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
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
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

theorem PI.IsoDetW.Loc.mulR_sat (p : Ideal R) [p.IsPrime] (a : K) (s : R) (y : K) (hs : s ∈ p.primeCompl)
    (hy : s • y ∈ LinearMap.range (mulR (R := R) a)) : y ∈ LinearMap.range (mulR (R := R) a) := by sorry
