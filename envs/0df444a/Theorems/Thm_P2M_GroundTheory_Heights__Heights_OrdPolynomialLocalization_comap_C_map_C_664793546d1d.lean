-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_comap_C_map_C_664793546d1d
-- name    : P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_comap_C_map_C_664793546d1d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:13.090498+00:00
-- url     : https://prove2.me/theorems/3dfd4fb4-c487-4b03-9a16-169a20e7b9e3
-- title:
--   P2 M Ground Theory Heights  Heights Ord Polynomial Localization comap C map C 664793546d1d: P2 M Ground Theory Heights  Heights Ord Polynomial Localization comap C map C 664793546d1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Ord Polynomial Localization comap C map C 664793546d1d construction uses the P2 M Ground Theory Heights  Heights Ord Polynomial Localization comap C map C 664793546d1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/POrdPolynomialLocalization.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/POrdPolynomialLocalization.lean#L9-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization
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
open MvPolynomial IsLocalRing

theorem P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_comap_C_map_C_664793546d1d {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) :
    Ideal.comap (C : R →+* MvPolynomial σ R) (Ideal.map (C : R →+* MvPolynomial σ R) p) = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrdPolynomialLocalization».«comap_C_map_C» := P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_comap_C_map_C_664793546d1d
