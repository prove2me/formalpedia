-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_add__e001087792f4
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_add__e001087792f4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:09.481918+00:00
-- url     : https://prove2.me/theorems/281dd3a9-38a5-43a6-a99e-afc15e703648
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog add  e001087792f4: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog add
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog add  e001087792f4 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog add  e001087792f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L32-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_add__036135b665a7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_add__e001087792f4 {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointResidue».«isMultiHomog_add'» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_add__e001087792f4
