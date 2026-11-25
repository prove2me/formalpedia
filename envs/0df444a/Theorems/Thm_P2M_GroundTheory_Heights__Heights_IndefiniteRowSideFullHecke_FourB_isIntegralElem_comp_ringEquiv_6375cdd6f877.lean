-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_isIntegralElem_comp_ringEquiv_6375cdd6f877
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_isIntegralElem_comp_ringEquiv_6375cdd6f877
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:39:42.471738+00:00
-- url     : https://prove2.me/theorems/73cdad98-d16f-403c-b24c-1bc082524175
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B is Integral Elem comp ring Equiv 6375cdd6f877: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B is In
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B is Integral Elem comp ring Equiv 6375cdd6f877 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B is Integral Elem comp ring Equiv 6375cdd6f877 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/NormLeOneIffIsIntegralElemOfEquiv.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/NormLeOneIffIsIntegralElemOfEquiv.lean#L12-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_isIntegralElem_comp_ringEquiv_6375cdd6f877 {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    (φ : A ≃+* B) (f : B →+* S) (x : S) :
    (f.comp (φ : A →+* B)).IsIntegralElem x ↔ f.IsIntegralElem x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«isIntegralElem_comp_ringEquiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_isIntegralElem_comp_ringEquiv_6375cdd6f877
