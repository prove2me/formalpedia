-- Prove2me | Theorems.Thm_PI_LocDualGen_Top_trQ_eq
-- name    : PI.LocDualGen.Top.trQ_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:06.660156+00:00
-- url     : https://prove2.me/theorems/7f61599f-a9a2-44c8-843e-af8ea8e6def4
-- title:
--   Top: tr Q eq
-- statement:
--   The Top construction uses the tr Q eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/PsiTower.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/PsiTower.lean#L20-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_PsiTower
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
open PI PI.LocDualGen PI.LocDualGen.Top
open PI.LocDualGen.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} [Fact (resChar p).Prime]

theorem PI.LocDualGen.Top.trQ_eq (A : LocAt F E sig p) (z : A.Ep) :
    (letI := qAlg A; Algebra.trace ℚ_[resChar p] A.Ep z) =
      Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep z) := by sorry
