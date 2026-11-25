-- Prove2me | Theorems.Thm_PI_PolynomialProperness_polyProper_of_steps
-- name    : PI.PolynomialProperness.polyProper_of_steps
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:02:43.926176+00:00
-- url     : https://prove2.me/theorems/ea5425a8-e4bb-5a23-a093-daae662c53c7
-- title:
--   Polynomial Properness: poly Proper of steps
-- statement:
--   The Polynomial Properness construction uses the poly Proper of steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L150-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L150-L176

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_AddLeMulPowOfSqLeOfLeMul
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

theorem PI.PolynomialProperness.polyProper_of_steps (hG : GVGroup) (hN : NormInv) (hNF : GNFacts) (hF : FmulBound)
    (hZ : ZhatMove) (hS : FrameS) (hSg : FrameSg) (hSg' : FrameSg') (hA : UnitriangularInversePolynomialBound)
    (hC : CoreInst) : PolyProper := by sorry
