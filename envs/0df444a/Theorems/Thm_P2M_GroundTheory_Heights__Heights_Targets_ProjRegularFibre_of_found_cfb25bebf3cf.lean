-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularFibre_of_found_cfb25bebf3cf
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegularFibre_of_found_cfb25bebf3cf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:31.781963+00:00
-- url     : https://prove2.me/theorems/6306fda5-0a4d-4dbc-b332-93729fc38407
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular Fibre of found cfb25bebf3cf: P2 M Ground Theory Heights  Heights Targets Proj Regular Fibre of found cfb25bebf3cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular Fibre of found cfb25bebf3cf construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular Fibre of found cfb25bebf3cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L84-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L84-L136

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularFibre
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegularFibre_of_found_cfb25bebf3cf (hReg : ProjRegular.Statement) : ProjRegularFibre.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegularFibre».«of_found» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegularFibre_of_found_cfb25bebf3cf
