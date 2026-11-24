-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Frob_intB_apply
-- name    : PositivityTheory.PfBern.Frob.intB_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:17.253799+00:00
-- url     : https://prove2.me/theorems/b2ced9e3-3452-46f2-8808-91447bd23ac9
-- title:
--   Frob: int B apply
-- statement:
--   The Frob construction uses the int B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/TensInduction.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/TensInduction.lean#L128-L130

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhatStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B]
  (μ : Measure B) [IsFiniteMeasureOnCompacts μ]

theorem PositivityTheory.PfBern.Frob.intB_apply (w : B → ℂ) (hw : Continuous w) (F : SB (A × B)) (a : A) :
    ((intB μ w hw F : SB A) : A → ℂ) a = ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ := by sorry

attribute [defeq] PositivityTheory.PfBern.Frob.intB_apply
