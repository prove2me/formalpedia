-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_EabLie_hpk_hh__b7503cf64b36
-- name    : P2M_Formalism_FourierDecayAlt_Q_EabLie_hpk_hh__b7503cf64b36
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:38:07.127684+00:00
-- url     : https://prove2.me/theorems/6d5237f4-4b27-442e-b2e9-061be7842714
-- title:
--   P2 M Formalism Fourier Decay Alt Q Eab Lie hpk hh  b7503cf64b36: P2 M Formalism Fourier Decay Alt Q Eab Lie hpk hh  b7503cf64b36
-- statement:
--   The P2 M Formalism Fourier Decay Alt Q Eab Lie hpk hh  b7503cf64b36 construction uses the P2 M Formalism Fourier Decay Alt Q Eab Lie hpk hh  b7503cf64b36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/HasDerivAtExt.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DerivativePreservation/HasDerivAtExt.lean#L28-L29

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_Q_EabLie_hpk_hh__b7503cf64b36 (A : Mx k r) : A * Hpk k r * Hpk k r = A := by sorry

alias «Formalism».«FourierDecayAlt».«Q».«EabLie».«hpk_hh'» := P2M_Formalism_FourierDecayAlt_Q_EabLie_hpk_hh__b7503cf64b36
