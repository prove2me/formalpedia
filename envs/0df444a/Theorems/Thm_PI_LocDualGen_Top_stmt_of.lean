-- Prove2me | Theorems.Thm_PI_LocDualGen_Top_stmt_of
-- name    : PI.LocDualGen.Top.stmt_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:09.671272+00:00
-- url     : https://prove2.me/theorems/f5bf83be-a787-48f3-90ac-b60662e0fb4c
-- title:
--   Top: stmt of
-- statement:
--   The Top construction uses the stmt of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/PsiTower.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/PsiTower.lean#L71-L82

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

theorem PI.LocDualGen.Top.stmt_of (hK : PsiKer) (h1 : FpDual) (h2 : FpDualUnram) (h3 : EpSelfDual) :
    PI.LocDualGen.Stmt := by sorry
