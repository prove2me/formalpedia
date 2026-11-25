-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_colon_span_singleton_eq_of_not_mem_585d56ee6b6a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_colon_span_singleton_eq_of_not_mem_585d56ee6b6a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:33.951798+00:00
-- url     : https://prove2.me/theorems/3a337f10-40cf-4c19-aa9f-132d62c91d92
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel colon span singleton eq of not mem 585d56ee6b6a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hi
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel colon span singleton eq of not mem 585d56ee6b6a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel colon span singleton eq of not mem 585d56ee6b6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ColonSpanSingletonEqOfNotMem.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ColonSpanSingletonEqOfNotMem.lean#L44-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_colon_span_singleton_eq_of_not_mem_585d56ee6b6a {R : Type*} [CommRing R] {q : Ideal R} [q.IsPrime]
    {s : R} (hs : s ∉ q) : q.colon (Ideal.span {s}) = q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HilbertSamuel».«colon_span_singleton_eq_of_not_mem» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_colon_span_singleton_eq_of_not_mem_585d56ee6b6a
