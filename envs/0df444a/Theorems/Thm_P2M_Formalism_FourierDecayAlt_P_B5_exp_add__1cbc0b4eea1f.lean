-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B5_exp_add__1cbc0b4eea1f
-- name    : P2M_Formalism_FourierDecayAlt_P_B5_exp_add__1cbc0b4eea1f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:16:04.756698+00:00
-- url     : https://prove2.me/theorems/43981d4e-a260-4e70-a224-7d68681cc8e4
-- title:
--   P2 M Formalism Fourier Decay Alt P B5 exp add  1cbc0b4eea1f: P2 M Formalism Fourier Decay Alt P B5 exp add  1cbc0b4eea1f
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B5 exp add  1cbc0b4eea1f construction uses the P2 M Formalism Fourier Decay Alt P B5 exp add  1cbc0b4eea1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L503-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L503-L506

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_B5_exp_add__1cbc0b4eea1f (X : Mat k r) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B5».«exp_add'» := P2M_Formalism_FourierDecayAlt_P_B5_exp_add__1cbc0b4eea1f
