-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_eq_zero_of_vanish_5a53e0f01f97
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_eq_zero_of_vanish_5a53e0f01f97
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:52.844995+00:00
-- url     : https://prove2.me/theorems/55b2890e-7764-40f3-b441-672506b9f391
-- title:
--   P2 M Ground Theory Heights  Heights Inter pts Integral eq zero of vanish 5a53e0f01f97: P2 M Ground Theory Heights  Heights Inter pts Integral eq zero of vanish 5a53e0f01f97
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pts Integral eq zero of vanish 5a53e0f01f97 construction uses the P2 M Ground Theory Heights  Heights Inter pts Integral eq zero of vanish 5a53e0f01f97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeSlotAdd.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeSlotAdd.lean#L19-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeSlotAdd
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_eq_zero_of_vanish_5a53e0f01f97 (P : Ideal (MRing ι)) {e : ℕ}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ z ∈ mcPts P, g z = 0) : ptsIntegral P φ g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ptsIntegral_eq_zero_of_vanish» := P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_eq_zero_of_vanish_5a53e0f01f97
