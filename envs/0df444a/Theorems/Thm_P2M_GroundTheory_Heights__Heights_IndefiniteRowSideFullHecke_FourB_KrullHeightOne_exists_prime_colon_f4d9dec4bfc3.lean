-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_KrullHeightOne_exists_prime_colon_f4d9dec4bfc3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_KrullHeightOne_exists_prime_colon_f4d9dec4bfc3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:38.604851+00:00
-- url     : https://prove2.me/theorems/c1dc5822-33e4-407c-9530-2bfa760b155a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Krull Height One exists prime colon f4d9dec4bfc3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Kr
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Krull Height One exists prime colon f4d9dec4bfc3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B Krull Height One exists prime colon f4d9dec4bfc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PKrullHeightOne.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PKrullHeightOne.lean#L11-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsKrullHeightOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PKrullHeightOne
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
open Ideal

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_KrullHeightOne_exists_prime_colon_f4d9dec4bfc3 {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p q : A) (hqp : ¬ q ∣ p) :
    ∃ (a : A) (P : Ideal A), P.IsPrime ∧ ¬ q ∣ a * p ∧ ∀ x, x ∈ P ↔ q ∣ x * (a * p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«KrullHeightOne».«exists_prime_colon» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_KrullHeightOne_exists_prime_colon_f4d9dec4bfc3
