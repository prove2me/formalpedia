-- Prove2me | Theorems.Thm_PI_LocGlobInclWork_smul_mem_idealSmul
-- name    : PI.LocGlobInclWork.smul_mem_idealSmul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:52.177476+00:00
-- url     : https://prove2.me/theorems/9660d6b1-3dcb-451f-9288-221dfa65f688
-- title:
--   Loc Glob Incl Work: smul mem ideal Smul
-- statement:
--   The Loc Glob Incl Work construction uses the smul mem ideal Smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L100-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalInclusion/SmulMemIdealSmul.lean#L100-L113

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K] {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W]

theorem PI.LocGlobInclWork.smul_mem_idealSmul (I J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (B : Submodule (𝓞 K) W) (t : 𝓞 K) (ht : algebraMap (𝓞 K) K t ∈ J) {y : W}
    (hy : y ∈ Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) B) :
    t • y ∈ Formalism.HermitianLatticesTheory.idealSmul ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) B := by sorry
