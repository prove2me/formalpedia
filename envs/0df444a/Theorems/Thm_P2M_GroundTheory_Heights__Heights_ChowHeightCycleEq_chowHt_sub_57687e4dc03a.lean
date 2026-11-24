-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_chowHt_sub_57687e4dc03a
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_chowHt_sub_57687e4dc03a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:22.702571+00:00
-- url     : https://prove2.me/theorems/f1e4f923-2093-4690-961d-52e386e75a43
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Cycle Eq chow Ht sub 57687e4dc03a: P2 M Ground Theory Heights  Heights Chow Height Cycle Eq chow Ht sub 57687e4dc03a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Cycle Eq chow Ht sub 57687e4dc03a construction uses the P2 M Ground Theory Heights  Heights Chow Height Cycle Eq chow Ht sub 57687e4dc03a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L17-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_chowHt_sub_57687e4dc03a {K : Type} [Field K] [NumberField K]
    (μ ν : InfinitePlace K → Measure (Fin (e + 1) × Fin n → ℂ))
    (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ P δ - ReciprocityTheory.ChartRestriction.G.Geo.chowHt ν P δ =
      (∑ w : InfinitePlace K, (w.mult : ℝ) *
        (ReciprocityTheory.ChartRestriction.G.Geo.logMean (μ w) (map w.embedding P) -
          ReciprocityTheory.ChartRestriction.G.Geo.logMean (ν w) (map w.embedding P))) / Height.totalWeight K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightCycleEq».«chowHt_sub» := P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_chowHt_sub_57687e4dc03a
