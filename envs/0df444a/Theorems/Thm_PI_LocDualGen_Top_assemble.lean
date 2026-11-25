-- Prove2me | Theorems.Thm_PI_LocDualGen_Top_assemble
-- name    : PI.LocDualGen.Top.assemble
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:15.120053+00:00
-- url     : https://prove2.me/theorems/25ed7526-47b3-5ba3-8a20-0900e704c8a3
-- title:
--   Top: assemble
-- statement:
--   The Top construction uses the assemble property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/PsiTower.lean#L42-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/PsiTower.lean#L42-L69

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

theorem PI.LocDualGen.Top.assemble (hK : PsiKer) (A : LocAt F E sig p) (d : A.Fp)
    (hd : ∀ a : A.Fp, (∀ b : 𝒪[A.Fp],
      ‖Algebra.trace ℚ_[resChar p] A.Fp (a * (b : A.Fp) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[A.Fp])
    (hE : ∀ x : A.Ep, (∀ y ∈ A.O, Algebra.trace A.Fp A.Ep (x * y) ∈ 𝒪[A.Fp]) ↔ x ∈ A.O) :
    DualAtL A d := by sorry
