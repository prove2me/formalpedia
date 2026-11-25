-- Prove2me | Theorems.Thm_PI_PolynomialProperness_polyProper5_of_steps
-- name    : PI.PolynomialProperness.polyProper5_of_steps
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:22:29.928714+00:00
-- url     : https://prove2.me/theorems/048b7dcf-1f8a-5b33-8e1f-98320308e4b0
-- title:
--   Polynomial Properness: poly Proper5 of steps
-- statement:
--   The Polynomial Properness construction uses the poly Proper5 of steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/PolyProper5OfSteps.lean#L19-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/PolyProper5OfSteps.lean#L19-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_PolyProperOfMx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_PolyProper5OfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness

theorem PI.PolynomialProperness.polyProper5_of_steps (hG : GVGroup) (hN : NormInv) (hNF : GNFacts) (hF : FmulBound)
    (hZ : ZhatMove) (hS : FrameS) (hSg : FrameSg) (hSg' : FrameSg') (hA : UnitriangularInversePolynomialBound)
    (hC : CoreInst) : PolyProper5 := by sorry
