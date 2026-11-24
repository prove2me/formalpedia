-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_localizedModule_quotient_map_06587b043cc3
-- name    : P2M_GroundTheory_Heights__Heights_length_localizedModule_quotient_map_06587b043cc3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:13.68647+00:00
-- url     : https://prove2.me/theorems/64d75c5a-e021-42b8-9eab-e943f3e8acd7
-- title:
--   P2 M Ground Theory Heights  Heights length localized Module quotient map 06587b043cc3: P2 M Ground Theory Heights  Heights length localized Module quotient map 06587b043cc3
-- statement:
--   The P2 M Ground Theory Heights  Heights length localized Module quotient map 06587b043cc3 construction uses the P2 M Ground Theory Heights  Heights length localized Module quotient map 06587b043cc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L151-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L151-L161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')
variable (J V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime]

theorem P2M_GroundTheory_Heights__Heights_length_localizedModule_quotient_map_06587b043cc3 :
    Module.length (Localization.AtPrime (V.map σ))
        (LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ)) =
      Module.length (Localization.AtPrime V) (LocalizedModule V.primeCompl (A ⧸ J)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_localizedModule_quotient_map» := P2M_GroundTheory_Heights__Heights_length_localizedModule_quotient_map_06587b043cc3
