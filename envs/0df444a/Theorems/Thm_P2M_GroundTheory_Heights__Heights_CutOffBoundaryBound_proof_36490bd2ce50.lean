-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_proof_36490bd2ce50
-- name    : P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_proof_36490bd2ce50
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:53.254007+00:00
-- url     : https://prove2.me/theorems/0d1a8eb2-f508-5860-b0d4-248d3374b2d9
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Boundary Bound proof 36490bd2ce50: P2 M Ground Theory Heights  Heights Cut Off Boundary Bound proof 36490bd2ce50
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Boundary Bound proof 36490bd2ce50 construction uses the P2 M Ground Theory Heights  Heights Cut Off Boundary Bound proof 36490bd2ce50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L199-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L199-L363

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffGradient_proof_81aaa98bdfc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open CutOffBoundaryBound

theorem P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_proof_36490bd2ce50 (hM : ChartMassCompact.Statement) (hL : MaDensLeibniz.Statement)
    (hN : EnergyDensNonneg.Statement) (hS : GradDensSheetBound.Statement) :
    CutOffBoundaryBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffBoundaryBound».«proof» := P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_proof_36490bd2ce50
