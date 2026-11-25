-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_mem_D_of_sameOrbit_6653390d49ce
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_mem_D_of_sameOrbit_6653390d49ce
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:19:04.607511+00:00
-- url     : https://prove2.me/theorems/f7789879-1b9e-5211-a7fe-70eef898700e
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge mem D of same Orbit 6653390d49ce: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge mem D of same Orbit 6653390d49ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge mem D of same Orbit 6653390d49ce construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge mem D of same Orbit 6653390d49ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullLift.lean#L25-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_mem_D_of_sameOrbit_6653390d49ce {z z' : (Σ k, ι k) → ℂ} (h : ReciprocityTheory.AnForm.R.SameOrbit z z')
    (hz' : z' ∈ ReciprocityTheory.AnForm.R.conePts R.D) : z ∈ ReciprocityTheory.AnForm.R.conePts R.D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«mem_D_of_sameOrbit» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_mem_D_of_sameOrbit_6653390d49ce
