-- Prove2me | Theorems.Thm_P2M_AlgebraicGeometry_Scheme_Opens_isClosedImmersion___of_isClosed_0d81dabaa08f
-- name    : P2M_AlgebraicGeometry_Scheme_Opens_isClosedImmersion___of_isClosed_0d81dabaa08f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:17.801116+00:00
-- url     : https://prove2.me/theorems/5683f1c4-caec-467e-87f4-4f58bfea5874
-- title:
--   P2 M Algebraic Geometry Scheme Opens is Closed Immersion   of is Closed 0d81dabaa08f: P2 M Algebraic Geometry Scheme Opens is Closed Immersion   of is Closed 0d81dabaa08f
-- statement:
--   The P2 M Algebraic Geometry Scheme Opens is Closed Immersion   of is Closed 0d81dabaa08f construction uses the P2 M Algebraic Geometry Scheme Opens is Closed Immersion   of is Closed 0d81dabaa08f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/ClopenSubscheme.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/ClopenSubscheme.lean#L9-L11

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens

theorem P2M_AlgebraicGeometry_Scheme_Opens_isClosedImmersion___of_isClosed_0d81dabaa08f {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsClosedImmersion U.ι := by sorry

alias «AlgebraicGeometry».«Scheme».«Opens».«isClosedImmersion_ι_of_isClosed» := P2M_AlgebraicGeometry_Scheme_Opens_isClosedImmersion___of_isClosed_0d81dabaa08f
