-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TPresMain_qnTPres_of__8193e22aa64f
-- name    : P2M_Formalism_FourierDecayAlt_Q_TPresMain_qnTPres_of__8193e22aa64f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:17.03949+00:00
-- url     : https://prove2.me/theorems/743dca63-85d2-5e5a-84bb-e1d9ac842ae2
-- title:
--   P2 M Formalism Fourier Decay Alt Q TPres Main qn TPres of  8193e22aa64f: P2 M Formalism Fourier Decay Alt Q TPres Main qn TPres of  8193e22aa64f
-- statement:
--   The P2 M Formalism Fourier Decay Alt Q TPres Main qn TPres of  8193e22aa64f construction uses the P2 M Formalism Fourier Decay Alt Q TPres Main qn TPres of  8193e22aa64f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/SecondCapelliMinorContinuousLinear.lean#L214-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/SecondCapelliMinorContinuousLinear.lean#L214-L215

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem P2M_Formalism_FourierDecayAlt_Q_TPresMain_qnTPres_of__8193e22aa64f (hT : TInvariant) (_ : EabPres) : TPreservesFF := by sorry

alias «Formalism».«FourierDecayAlt».«Q».«TPresMain».«qnTPres_of'» := P2M_Formalism_FourierDecayAlt_Q_TPresMain_qnTPres_of__8193e22aa64f
