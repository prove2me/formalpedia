-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_HX_basisInt
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.HX.basisInt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:42:58.992793+00:00
-- url     : https://prove2.me/theorems/fd105313-6387-43aa-8c68-edd01f0e2072
-- title:
--   HX: basis Int
-- statement:
--   The HX construction uses the basis Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L143-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L143-L152

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_TcoordBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
open PI.UnitaryGroupMassFormula.UJClassMass.HX
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassMass.HX.basisInt {ι : Type} [Fintype ι] (B : Module.Basis ι F E) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k, IsIntegral ℤ ((n : E) * B k) := by sorry
