-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TPresMain_sl_sum__cd5de3938d2f
-- name    : P2M_Formalism_FourierDecayAlt_Q_TPresMain_sl_sum__cd5de3938d2f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:37:50.156015+00:00
-- url     : https://prove2.me/theorems/cfec55e9-a0ed-4e17-8520-588ca6a34e97
-- title:
--   P2 M Formalism Fourier Decay Alt Q TPres Main sl sum  cd5de3938d2f: P2 M Formalism Fourier Decay Alt Q TPres Main sl sum  cd5de3938d2f
-- statement:
--   The P2 M Formalism Fourier Decay Alt Q TPres Main sl sum  cd5de3938d2f construction uses the P2 M Formalism Fourier Decay Alt Q TPres Main sl sum  cd5de3938d2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean#L75-L81

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_Q_TPresMain_sl_sum__cd5de3938d2f {ι : Type*} [Fintype ι] (f : ι → Mx k r → E) (hf : ∀ j, SmoothLev k r i D (f j)) :
    SmoothLev k r i D (fun x => ∑ j, f j x) := by sorry

alias «Formalism».«FourierDecayAlt».«Q».«TPresMain».«sl_sum'» := P2M_Formalism_FourierDecayAlt_Q_TPresMain_sl_sum__cd5de3938d2f
