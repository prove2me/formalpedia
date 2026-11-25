-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_quotientMap_surjective_89fc8fe2747e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_quotientMap_surjective_89fc8fe2747e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:57:00.888794+00:00
-- url     : https://prove2.me/theorems/2fb3c691-53cc-41cc-86db-8a32d7d31e1a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Localize Subvar quotient Map surjective 89fc8fe2747e: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Loca
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Localize Subvar quotient Map surjective 89fc8fe2747e construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Localize Subvar quotient Map surjective 89fc8fe2747e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLocalizeSubvar.lean#L16-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLocalizeSubvar.lean#L16-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeSubvarSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLocalizeSubvar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_quotientMap_surjective_89fc8fe2747e (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal]
    (O : Type) [CommRing O] [Algebra S O] [IsLocalization.AtPrime O 𝔪] (N : ℕ)
    (pp' : Ideal (Kleiman.Poly O N))
    (hle : (𝔪.map (algebraMap S O)).map (C : O →+* Kleiman.Poly O N) ≤ pp') :
    Function.Surjective (Ideal.quotientMap pp'
      (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N) le_rfl) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«LocalizeSubvar».«quotientMap_surjective» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_quotientMap_surjective_89fc8fe2747e
