-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_lidx_pi_frac
-- name    : PI.IsoDetW.Loc.lidx_pi_frac
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:24.660808+00:00
-- url     : https://prove2.me/theorems/5fe99a42-8377-5248-a9ac-2f82039b28d4
-- title:
--   Loc: lidx pi frac
-- statement:
--   The Loc construction uses the lidx pi frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L154-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L154-L182

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
omit [DecidableEq ι]

theorem PI.IsoDetW.Loc.lidx_pi_frac (P : HeightOneSpectrum R) (c b : ι → FI) (hc : ∀ i, c i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    lidx P.asIdeal (Submodule.pi Set.univ (fun i => (c i : Submodule R K)))
      (Submodule.pi Set.univ (fun i => (b i : Submodule R K))) =
      ∑ i, (FractionalIdeal.count K P (b i) - FractionalIdeal.count K P (c i)) := by sorry
