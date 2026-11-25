-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_int_quotient_map_5647412ff0d4
-- name    : P2M_GroundTheory_Heights__Heights_length_int_quotient_map_5647412ff0d4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:24.964617+00:00
-- url     : https://prove2.me/theorems/bc7879d3-0328-4b6c-8bf3-dd4447712723
-- title:
--   P2 M Ground Theory Heights  Heights length int quotient map 5647412ff0d4: P2 M Ground Theory Heights  Heights length int quotient map 5647412ff0d4
-- statement:
--   The P2 M Ground Theory Heights  Heights length int quotient map 5647412ff0d4 construction uses the P2 M Ground Theory Heights  Heights length int quotient map 5647412ff0d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L35-L37

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

theorem P2M_GroundTheory_Heights__Heights_length_int_quotient_map_5647412ff0d4 (I : Ideal A) :
    Module.length ℤ (A' ⧸ I.map σ) = Module.length ℤ (A ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_int_quotient_map» := P2M_GroundTheory_Heights__Heights_length_int_quotient_map_5647412ff0d4
