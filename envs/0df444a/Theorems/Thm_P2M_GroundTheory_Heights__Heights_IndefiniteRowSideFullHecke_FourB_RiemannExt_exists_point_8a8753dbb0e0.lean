-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_exists_point_8a8753dbb0e0
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_exists_point_8a8753dbb0e0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:21.293175+00:00
-- url     : https://prove2.me/theorems/8785fbc0-9c73-4669-816a-f505aaf0e5c4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Riemann Ext exists point 8a8753dbb0e0: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Riemann Ext e
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Riemann Ext exists point 8a8753dbb0e0 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Riemann Ext exists point 8a8753dbb0e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PRiemannExtension.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PRiemannExtension.lean#L11-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsKrullHeightOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PRiemannExtension
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_exists_point_8a8753dbb0e0 {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (P : Ideal A) [P.IsPrime] (c : A) (hc : c ∉ P) :
    ∃ x : A →ₐ[ℂ] ℂ, (∀ a ∈ P, x a = 0) ∧ x c ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«RiemannExt».«exists_point» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_exists_point_8a8753dbb0e0
