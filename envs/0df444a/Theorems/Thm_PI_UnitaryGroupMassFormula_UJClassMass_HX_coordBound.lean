-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_HX_coordBound
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.HX.coordBound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:15.235802+00:00
-- url     : https://prove2.me/theorems/63b7aa5e-37ff-5489-b8a0-ceb654db97e7
-- title:
--   HX: coord Bound
-- statement:
--   The HX construction uses the coord Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L117-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L117-L141

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.HX.coordBound {ι : Type} [Fintype ι] (B : Module.Basis ι F E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ PI.UnitaryApproxDefs.intOE E, ∀ k, IsIntegral ℤ ((m : F) * B.coord k x) := by sorry
