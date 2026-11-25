-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cs_LR
-- name    : PI.UnitaryCorollaryDerivatives.CRH.cs_LR
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:39:48.996804+00:00
-- url     : https://prove2.me/theorems/040f6690-ce9c-48eb-bd03-24537cd08273
-- title:
--   CRH: cs LR
-- statement:
--   The CRH construction uses the cs LR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRB.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRB.lean#L25-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.CRH.cs_LR (cost : Mat k r → ℕ) (u v : List (Mat k r)) :
    ((u ++ v).map cost).sum = cs cost (wL u ++ wR v) := by sorry
