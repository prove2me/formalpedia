-- Prove2me | Theorems.Thm_PI_HtGenericPt_Pf_main
-- name    : PI.HtGenericPt.Pf.main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:45:40.692951+00:00
-- url     : https://prove2.me/theorems/8cc82955-00aa-57f9-9d3d-d55039ec829d
-- title:
--   Pf: main
-- statement:
--   The Pf construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GenericPointHeight/GenericPointStatements/GenericPointLemmas/GenericPointWeights/Wx.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GenericPointHeight/GenericPointStatements/GenericPointLemmas/GenericPointWeights/Wx.lean#L7-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GenericPointHeight_GenericPointStatements_GenericPointLemmas_GenericPointWeights_Wx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.HtGenericPt PI.HtGenericPt.Pf

theorem PI.HtGenericPt.Pf.main {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.exists_generic 𝒜 d := by sorry
