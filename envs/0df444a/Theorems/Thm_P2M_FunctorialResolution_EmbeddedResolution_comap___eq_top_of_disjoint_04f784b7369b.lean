-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_comap___eq_top_of_disjoint_04f784b7369b
-- name    : P2M_FunctorialResolution_EmbeddedResolution_comap___eq_top_of_disjoint_04f784b7369b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:31.767829+00:00
-- url     : https://prove2.me/theorems/7bfe019b-c85b-42bb-97c0-7395c52cbe8e
-- title:
--   P2 M Functorial Resolution Embedded Resolution comap   eq top of disjoint 04f784b7369b: P2 M Functorial Resolution Embedded Resolution comap   eq top of disjoint 04f784b7369b
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution comap   eq top of disjoint 04f784b7369b construction uses the P2 M Functorial Resolution Embedded Resolution comap   eq top of disjoint 04f784b7369b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L130-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L130-L140

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry

theorem P2M_FunctorialResolution_EmbeddedResolution_comap___eq_top_of_disjoint_04f784b7369b {X : Scheme} (I : X.IdealSheafData) (U : X.Opens)
    (h : Disjoint (U : Set X) (I.support : Set X)) : I.comap U.ι = ⊤ := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«comap_ι_eq_top_of_disjoint» := P2M_FunctorialResolution_EmbeddedResolution_comap___eq_top_of_disjoint_04f784b7369b
