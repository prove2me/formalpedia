-- Prove2me | Theorems.Thm_P2M_PI_FJMX_shapeProd_der__29b51981dd02
-- name    : P2M_PI_FJMX_shapeProd_der__29b51981dd02
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:57:08.240594+00:00
-- url     : https://prove2.me/theorems/de3e773a-a863-4f45-b763-e39cb9d86b29
-- title:
--   P2 M PI FJMX shape Prod der  29b51981dd02: P2 M PI FJMX shape Prod der  29b51981dd02
-- statement:
--   The P2 M PI FJMX shape Prod der  29b51981dd02 construction uses the P2 M PI FJMX shape Prod der  29b51981dd02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L65-L70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {A : Type*} [CommRing A] [Algebra ℂ A] {m k : ℕ}

theorem P2M_PI_FJMX_shapeProd_der__29b51981dd02 (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (α : List ℕ)
    (h : ∀ t, D (PI.FJM.leadT M t) = 0) : D (PI.FJM.shapeProd M α) = 0 := by sorry

alias «PI».«FJMX».«shapeProd_der'» := P2M_PI_FJMX_shapeProd_der__29b51981dd02
