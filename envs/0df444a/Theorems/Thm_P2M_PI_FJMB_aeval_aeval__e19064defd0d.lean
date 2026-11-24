-- Prove2me | Theorems.Thm_P2M_PI_FJMB_aeval_aeval__e19064defd0d
-- name    : P2M_PI_FJMB_aeval_aeval__e19064defd0d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:29.401538+00:00
-- url     : https://prove2.me/theorems/ca5369bc-12a8-4e4f-8628-a3b68e0c009d
-- title:
--   P2 M PI FJMB aeval aeval  e19064defd0d: P2 M PI FJMB aeval aeval  e19064defd0d
-- statement:
--   The P2 M PI FJMB aeval aeval  e19064defd0d construction uses the P2 M PI FJMB aeval aeval  e19064defd0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L21-L26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}

theorem P2M_PI_FJMB_aeval_aeval__e19064defd0d {K : Type*} [CommRing K] [Algebra ℂ K] (g : σ → K) (φ : σ → MvPolynomial σ ℂ)
    (f : MvPolynomial σ ℂ) : aeval g (aeval φ f) = aeval (fun v => aeval g (φ v)) f := by sorry

alias «PI».«FJMB».«aeval_aeval'» := P2M_PI_FJMB_aeval_aeval__e19064defd0d
