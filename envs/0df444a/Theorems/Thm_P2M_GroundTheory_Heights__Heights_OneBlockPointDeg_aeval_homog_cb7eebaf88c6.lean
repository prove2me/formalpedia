-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_aeval_homog_cb7eebaf88c6
-- name    : P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_aeval_homog_cb7eebaf88c6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:06.604206+00:00
-- url     : https://prove2.me/theorems/4d0cb0b3-f830-4aa9-a8ff-7bb7dca14269
-- title:
--   P2 M Ground Theory Heights  Heights One Block Point Deg aeval homog cb7eebaf88c6: P2 M Ground Theory Heights  Heights One Block Point Deg aeval homog cb7eebaf88c6
-- statement:
--   The P2 M Ground Theory Heights  Heights One Block Point Deg aeval homog cb7eebaf88c6 construction uses the P2 M Ground Theory Heights  Heights One Block Point Deg aeval homog cb7eebaf88c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POneBlockPointDeg.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/POneBlockPointDeg.lean#L28-L36

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

theorem P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_aeval_homog_cb7eebaf88c6 (hK : ∀ k, k = k₀) {w : (Σ k, ι k) → Φ'} {c : ∀ k, ι k} (hc : w ⟨k₀, c k₀⟩ ≠ 0)
    {g : MRingOver Φ ι} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun p => w p / w ⟨k₀, c k₀⟩) g * w ⟨k₀, c k₀⟩ ^ n = aeval w g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OneBlockPointDeg».«aeval_homog» := P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_aeval_homog_cb7eebaf88c6
