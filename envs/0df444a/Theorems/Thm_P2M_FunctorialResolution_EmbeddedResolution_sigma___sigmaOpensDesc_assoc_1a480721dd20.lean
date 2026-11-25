-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_assoc_1a480721dd20
-- name    : P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_assoc_1a480721dd20
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:35.382581+00:00
-- url     : https://prove2.me/theorems/3f814d1f-660a-4d21-9c05-6d06e4c3dc60
-- title:
--   P2 M Functorial Resolution Embedded Resolution sigma   sigma Opens Desc assoc 1a480721dd20: P2 M Functorial Resolution Embedded Resolution sigma   sigma Opens Desc assoc 1a480721dd20
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution sigma   sigma Opens Desc assoc 1a480721dd20 construction uses the P2 M Functorial Resolution Embedded Resolution sigma   sigma Opens Desc assoc 1a480721dd20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L20-L23

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

theorem P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_assoc_1a480721dd20 (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) (i : ι)
    {Z : Scheme.{u}} (h : Y ⟶ Z) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U ≫ h = (U i).ι ≫ h := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«sigma_ι_sigmaOpensDesc_assoc» := P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_assoc_1a480721dd20
