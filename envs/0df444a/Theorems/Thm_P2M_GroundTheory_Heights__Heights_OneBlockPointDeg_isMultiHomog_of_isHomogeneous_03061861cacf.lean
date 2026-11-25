-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_isMultiHomog_of_isHomogeneous_03061861cacf
-- name    : P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_isMultiHomog_of_isHomogeneous_03061861cacf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:54:08.239777+00:00
-- url     : https://prove2.me/theorems/0c77db29-c746-4a26-bd85-d465eb001872
-- title:
--   P2 M Ground Theory Heights  Heights One Block Point Deg is Multi Homog of is Homogeneous 03061861cacf: P2 M Ground Theory Heights  Heights One Block Point Deg is Multi Homog of is Homogeneous 03061861
-- statement:
--   The P2 M Ground Theory Heights  Heights One Block Point Deg is Multi Homog of is Homogeneous 03061861cacf construction uses the P2 M Ground Theory Heights  Heights One Block Point Deg is Multi Homog of is Homogeneous 03061861cacf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POneBlockPointDeg.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POneBlockPointDeg.lean#L18-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POneBlockPointDeg
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
open GroundTheory.Heights₂.Heights.OneBlockPointDeg
variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}

theorem P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_isMultiHomog_of_isHomogeneous_03061861cacf (hK : ∀ k, k = k₀) {f : MRingOver Φ ι} {n : ℕ}
    (hf : f.IsHomogeneous n) : IsMultiHomog f fun _ => n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OneBlockPointDeg».«isMultiHomog_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_isMultiHomog_of_isHomogeneous_03061861cacf
