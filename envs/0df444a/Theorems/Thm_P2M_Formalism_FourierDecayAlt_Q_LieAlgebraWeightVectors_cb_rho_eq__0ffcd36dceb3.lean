-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_eq__0ffcd36dceb3
-- name    : P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_eq__0ffcd36dceb3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:45:58.650879+00:00
-- url     : https://prove2.me/theorems/fbd6a4fe-32c3-4b30-9e3f-3f4dd708174f
-- title:
--   P2 M Formalism Fourier Decay Alt Q Lie Algebra Weight Vectors cb rho eq  0ffcd36dceb3: P2 M Formalism Fourier Decay Alt Q Lie Algebra Weight Vectors cb rho eq  0ffcd36dceb3
-- statement:
--   The P2 M Formalism Fourier Decay Alt Q Lie Algebra Weight Vectors cb rho eq  0ffcd36dceb3 construction uses the P2 M Formalism Fourier Decay Alt Q Lie Algebra Weight Vectors cb rho eq  0ffcd36dceb3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L72-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L72-L78

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_eq__0ffcd36dceb3 (Q : M.Par) (π : M.Ty Q) (j : Fin (Q.k - 1)) :
    M.rho Q π (j.1 + 1) = Q.lo (j.1 + 1) + (((π j : Fin _) : ℕ) : ℝ) := by sorry

alias «Formalism».«FourierDecayAlt».«Q».«LieAlgebraWeightVectors».«cb_rho_eq'» := P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_eq__0ffcd36dceb3
