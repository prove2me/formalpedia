-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagIdealOver_map_6cb9b06c5951
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagIdealOver_map_6cb9b06c5951
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:34.139318+00:00
-- url     : https://prove2.me/theorems/949fcf61-21ed-5b3e-ab1c-cf7cd33a74b0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Ideal Over map 6cb9b06c5951: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Ideal Over map
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Ideal Over map 6cb9b06c5951 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Ideal Over map 6cb9b06c5951 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagFibre.lean#L205-L209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagFibre
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagIdealOver_map_6cb9b06c5951 (hRel : RelBaseChange.Statement) (F F' : Type) [Field F] [Field F'] [Algebra F F'] :
    (flagIdealOver F n).map (MvPolynomial.map (algebraMap F F')) = flagIdealOver F' n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«flagIdealOver_map» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagIdealOver_map_6cb9b06c5951
