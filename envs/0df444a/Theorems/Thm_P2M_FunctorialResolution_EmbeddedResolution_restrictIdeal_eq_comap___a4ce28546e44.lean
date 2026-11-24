-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
-- name    : P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:22.197616+00:00
-- url     : https://prove2.me/theorems/c6e7927a-72cb-4a72-b41e-33495035eead
-- title:
--   P2 M Functorial Resolution Embedded Resolution restrict Ideal eq comap   a4ce28546e44: P2 M Functorial Resolution Embedded Resolution restrict Ideal eq comap   a4ce28546e44
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution restrict Ideal eq comap   a4ce28546e44 construction uses the P2 M Functorial Resolution Embedded Resolution restrict Ideal eq comap   a4ce28546e44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L16-L17

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44 {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal I U = I.comap U.ι := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«restrictIdeal_eq_comap_ι» := P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
