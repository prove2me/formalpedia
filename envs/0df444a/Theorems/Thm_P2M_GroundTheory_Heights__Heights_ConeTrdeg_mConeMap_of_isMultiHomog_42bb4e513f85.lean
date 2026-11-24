-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTrdeg_mConeMap_of_isMultiHomog_42bb4e513f85
-- name    : P2M_GroundTheory_Heights__Heights_ConeTrdeg_mConeMap_of_isMultiHomog_42bb4e513f85
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:44.462936+00:00
-- url     : https://prove2.me/theorems/9cba1d8f-bb24-4356-89fe-49e2b79fe637
-- title:
--   P2 M Ground Theory Heights  Heights Cone Trdeg m Cone Map of is Multi Homog 42bb4e513f85: P2 M Ground Theory Heights  Heights Cone Trdeg m Cone Map of is Multi Homog 42bb4e513f85
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Trdeg m Cone Map of is Multi Homog 42bb4e513f85 construction uses the P2 M Ground Theory Heights  Heights Cone Trdeg m Cone Map of is Multi Homog 42bb4e513f85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PConeTrdeg.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PConeTrdeg.lean#L13-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_ConeTrdeg_mConeMap_of_isMultiHomog_42bb4e513f85 (y : (Σ k, ι k) → Ω) {g : Geo.MRing ι} {d : K → ℕ}
    (hg : Geo.IsMultiHomog g d) :
    Geo.mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, X k ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeTrdeg».«mConeMap_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_ConeTrdeg_mConeMap_of_isMultiHomog_42bb4e513f85
