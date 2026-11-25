-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_segre_of_sameOrbit_2b78d385d421
-- name    : P2M_GroundTheory_Heights__Heights_Targets_segre_of_sameOrbit_2b78d385d421
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:59.604878+00:00
-- url     : https://prove2.me/theorems/ccdeeeeb-b83d-53a3-a623-5d0ec5dab82a
-- title:
--   P2 M Ground Theory Heights  Heights Targets segre of same Orbit 2b78d385d421: P2 M Ground Theory Heights  Heights Targets segre of same Orbit 2b78d385d421
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets segre of same Orbit 2b78d385d421 construction uses the P2 M Ground Theory Heights  Heights Targets segre of same Orbit 2b78d385d421 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L19-L24

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_segre_of_sameOrbit_2b78d385d421 {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ∃ c : ℂ, c ≠ 0 ∧ segre z = c • (segre z' : ((k : K) → ι k) → ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«segre_of_sameOrbit» := P2M_GroundTheory_Heights__Heights_Targets_segre_of_sameOrbit_2b78d385d421
