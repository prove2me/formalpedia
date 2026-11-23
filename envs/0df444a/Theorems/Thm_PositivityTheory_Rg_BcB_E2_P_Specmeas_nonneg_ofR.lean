-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_nonneg_ofR
-- name    : PositivityTheory.Rg.BcB.E2.P.Specmeas.nonneg_ofR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:38.709083+00:00
-- url     : https://prove2.me/theorems/80410311-9e93-4387-9134-c3dd04753739
-- title:
--   Specmeas: nonneg of R
-- statement:
--   The Specmeas construction uses the nonneg of R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Specmeas.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Specmeas.lean#L36-L43

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P PositivityTheory.Rg.BcB.E2.P.Specmeas
variable {X : Type} [TopologicalSpace X]
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ

theorem PositivityTheory.Rg.BcB.E2.P.Specmeas.nonneg_ofR {g : C(X, ℝ)} (hg : ∀ x, 0 ≤ g x) : 0 ≤ Λ (ofR g) := by sorry
