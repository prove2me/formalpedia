-- Prove2me | Theorems.Thm_PI_LocDualGen_Part2_alg_mem_O
-- name    : PI.LocDualGen.Part2.alg_mem_O
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:26.665797+00:00
-- url     : https://prove2.me/theorems/8223ebc1-958d-413b-bb1f-70406925435c
-- title:
--   Part2: alg mem O
-- statement:
--   The Part2 construction uses the alg mem O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/DualAtLMulUnit.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/DualAtLMulUnit.lean#L12-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocDualGen PI.LocDualGen.Part2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

theorem PI.LocDualGen.Part2.alg_mem_O (r : 𝒪[A.Fp]) : algebraMap A.Fp A.Ep (r : A.Fp) ∈ A.O := by sorry
