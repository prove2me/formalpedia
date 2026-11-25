-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_length_map_8e436c9e22c2
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_length_map_8e436c9e22c2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:23.058925+00:00
-- url     : https://prove2.me/theorems/90101014-ca7e-46c7-b495-8f4e127e6e3e
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel length map 8e436c9e22c2: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel length map 8e436c9e22c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel length map 8e436c9e22c2 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel length map 8e436c9e22c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L40-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L40-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_length_map_8e436c9e22c2 (V W : Ideal R) [W.IsPrime] [(W.map (φ : R →+* R')).IsPrime] (hVW : V ≤ W)
    (x : R) :
    Module.length (Localization.AtPrime (W.map (φ : R →+* R')))
        (LocalizedModule (W.map (φ : R →+* R')).primeCompl
          (R' ⧸ (V.map (φ : R →+* R') ⊔ Ideal.span {φ x}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ (V ⊔ Ideal.span {x}))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«length_map» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_length_map_8e436c9e22c2
