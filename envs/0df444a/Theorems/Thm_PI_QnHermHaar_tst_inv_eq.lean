-- Prove2me | Theorems.Thm_PI_QnHermHaar_tst_inv_eq
-- name    : PI.QnHermHaar.tst_inv_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:18:44.914733+00:00
-- url     : https://prove2.me/theorems/0bfc1386-e0d5-4e25-ad45-ece44dff814c
-- title:
--   Qn Herm Haar: tst inv eq
-- statement:
--   The Qn Herm Haar construction uses the tst inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorPreservesTest.lean#L307-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorPreservesTest.lean#L307-L312

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.QnHermHaar.tst_inv_eq {k r : ℕ} {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by sorry
