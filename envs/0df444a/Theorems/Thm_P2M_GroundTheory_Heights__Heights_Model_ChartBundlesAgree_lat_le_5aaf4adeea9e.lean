-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_lat_le_5aaf4adeea9e
-- name    : P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_lat_le_5aaf4adeea9e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:49:33.290563+00:00
-- url     : https://prove2.me/theorems/f2db8468-f539-4337-8f31-2b40dbb092c4
-- title:
--   P2 M Ground Theory Heights  Heights Model Chart Bundles Agree lat le 5aaf4adeea9e: P2 M Ground Theory Heights  Heights Model Chart Bundles Agree lat le 5aaf4adeea9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Chart Bundles Agree lat le 5aaf4adeea9e construction uses the P2 M Ground Theory Heights  Heights Model Chart Bundles Agree lat le 5aaf4adeea9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PChartBundlesAgree.lean#L12-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PChartBundlesAgree.lean#L12-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PAwayHeightOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PChartBundlesAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_lat_le_5aaf4adeea9e (hHOI : HeightOneIntersection.Statement)
    {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] (B B' : ChartBundle o x r E) (i : τ) (hi : x i ≠ 0)
    (hN : IsNoetherianRing (chartRing o x i)) (hIC : IsIntegrallyClosed (chartRing o x i))
    (h1 : ∀ v ∈ B.lat i, ∃ s : chartRing o x i, s ≠ 0 ∧ (s : Ω) • v ∈ B'.lat i)
    (hq : ∀ q : Ideal (chartRing o x i), q.IsPrime → q.height = 1 → ∀ v : E,
      (∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B.lat i) →
        ∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B'.lat i) :
    B.lat i ≤ B'.lat i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«ChartBundlesAgree».«lat_le» := P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_lat_le_5aaf4adeea9e
