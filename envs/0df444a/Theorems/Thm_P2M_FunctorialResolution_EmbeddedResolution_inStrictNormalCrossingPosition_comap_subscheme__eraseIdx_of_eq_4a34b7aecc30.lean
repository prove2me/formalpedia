-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_comap_subscheme__eraseIdx_of_eq_4a34b7aecc30
-- name    : P2M_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_comap_subscheme__eraseIdx_of_eq_4a34b7aecc30
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:18.955032+00:00
-- url     : https://prove2.me/theorems/bf9acace-0188-4aef-86fc-ef6946b36615
-- title:
--   P2 M Functorial Resolution Embedded Resolution in Strict Normal Crossing Position comap subscheme  erase Idx of eq 4a34b7aecc30: P2 M Functorial Resolution Embedded Resolution in Strict Normal Crossin
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution in Strict Normal Crossing Position comap subscheme  erase Idx of eq 4a34b7aecc30 construction uses the P2 M Functorial Resolution Embedded Resolution in Strict Normal Crossing Position comap subscheme  erase Idx of eq 4a34b7aecc30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/StrictNormalCrossingsEraseMember.lean#L193-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/StrictNormalCrossingsEraseMember.lean#L193-L199

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_StrictNormalCrossingsEraseMember
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem P2M_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_comap_subscheme__eraseIdx_of_eq_4a34b7aecc30 {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) (D : X.IdealSheafData) (hD : E[j]'hj = D) :
    InStrictNormalCrossingPosition (D.subschemeι ≫ p)
      ((E.eraseIdx j).map fun F => F.comap D.subschemeι) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx_of_eq» := P2M_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_comap_subscheme__eraseIdx_of_eq_4a34b7aecc30
