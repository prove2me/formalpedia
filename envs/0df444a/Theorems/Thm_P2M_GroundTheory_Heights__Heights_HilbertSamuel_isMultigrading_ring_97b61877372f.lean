-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultigrading_ring_97b61877372f
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultigrading_ring_97b61877372f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:16.874191+00:00
-- url     : https://prove2.me/theorems/e1f6c4e0-5c99-413b-96f2-2fd647159f65
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel is Multigrading ring 97b61877372f: P2 M Ground Theory Heights  Heights Hilbert Samuel is Multigrading ring 97b61877372f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel is Multigrading ring 97b61877372f construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel is Multigrading ring 97b61877372f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsHilbert.lean#L160-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsHilbert.lean#L160-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type u} [Field F]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultigrading_ring_97b61877372f : IsMultigrading ι (MRing ι F) (ringPiece (F := F) (ι := ι)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«isMultigrading_ring» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultigrading_ring_97b61877372f
