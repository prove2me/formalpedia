-- Prove2me | Theorems.Thm_PI_LocDualGen_Top_psi_tower
-- name    : PI.LocDualGen.Top.psi_tower
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:44.920418+00:00
-- url     : https://prove2.me/theorems/ee823664-c011-433d-b9b7-e94541711865
-- title:
--   Top: psi tower
-- statement:
--   The Top construction uses the psi tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/PsiTower.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/PsiTower.lean#L30-L36

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

theorem PI.LocDualGen.Top.psi_tower (hK : PsiKer) (A : LocAt F E sig p) (z : A.Ep) :
    A.psiE z = 1 ↔ ‖Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep z)‖ ≤ 1 := by sorry
