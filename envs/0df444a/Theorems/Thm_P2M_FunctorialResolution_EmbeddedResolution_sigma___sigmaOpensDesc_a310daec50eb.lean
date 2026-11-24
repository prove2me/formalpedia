-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_a310daec50eb
-- name    : P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_a310daec50eb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:35.483815+00:00
-- url     : https://prove2.me/theorems/8126e0c7-2f9f-4701-9ebd-302d0af02302
-- title:
--   P2 M Functorial Resolution Embedded Resolution sigma   sigma Opens Desc a310daec50eb: P2 M Functorial Resolution Embedded Resolution sigma   sigma Opens Desc a310daec50eb
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution sigma   sigma Opens Desc a310daec50eb construction uses the P2 M Functorial Resolution Embedded Resolution sigma   sigma Opens Desc a310daec50eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L16-L18

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u

theorem P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_a310daec50eb (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) (i : ι) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U = (U i).ι := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«sigma_ι_sigmaOpensDesc» := P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_a310daec50eb
