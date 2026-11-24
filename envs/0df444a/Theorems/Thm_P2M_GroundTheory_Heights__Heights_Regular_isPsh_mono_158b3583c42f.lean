-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isPsh_mono_158b3583c42f
-- name    : P2M_GroundTheory_Heights__Heights_Regular_isPsh_mono_158b3583c42f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:08.127847+00:00
-- url     : https://prove2.me/theorems/ce9210e0-6fd5-4d11-9d11-6d0b74461342
-- title:
--   P2 M Ground Theory Heights  Heights Regular is Psh mono 158b3583c42f: P2 M Ground Theory Heights  Heights Regular is Psh mono 158b3583c42f
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular is Psh mono 158b3583c42f construction uses the P2 M Ground Theory Heights  Heights Regular is Psh mono 158b3583c42f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L301-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L301-L303

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_isPsh_mono_158b3583c42f {D : ℕ} {U V : Set (Fin D → ℂ)} {u : (Fin D → ℂ) → ℝ} (h : IsPsh U u)
    (hVU : V ⊆ U) : IsPsh V u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«isPsh_mono» := P2M_GroundTheory_Heights__Heights_Regular_isPsh_mono_158b3583c42f
