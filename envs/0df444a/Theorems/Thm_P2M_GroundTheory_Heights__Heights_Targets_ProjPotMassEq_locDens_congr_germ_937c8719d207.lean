-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_locDens_congr_germ_937c8719d207
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_locDens_congr_germ_937c8719d207
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:00.674904+00:00
-- url     : https://prove2.me/theorems/96bc3d12-b979-57be-874d-ecbed4745140
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq loc Dens congr germ 937c8719d207: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq loc Dens congr germ 937c8719d207
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq loc Dens congr germ 937c8719d207 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq loc Dens congr germ 937c8719d207 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L46-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_locDens_congr_germ_937c8719d207 (A : FinHolAtlas e X) (P Q : LocPot X) (j : Fin A.n) (y : Fin e → ℂ)
    (h : (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y')) :
    locDens A (fun _ => P) j y = locDens A (fun _ => Q) j y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«locDens_congr_germ» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_locDens_congr_germ_937c8719d207
