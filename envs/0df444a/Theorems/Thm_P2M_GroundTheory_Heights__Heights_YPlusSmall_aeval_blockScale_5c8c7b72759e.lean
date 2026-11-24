-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_blockScale_5c8c7b72759e
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_blockScale_5c8c7b72759e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:43.565941+00:00
-- url     : https://prove2.me/theorems/3f35a9a9-33c4-40f4-9a31-4f0c521adebc
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Small aeval block Scale 5c8c7b72759e: P2 M Ground Theory Heights  Heights YPlus Small aeval block Scale 5c8c7b72759e
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Small aeval block Scale 5c8c7b72759e construction uses the P2 M Ground Theory Heights  Heights YPlus Small aeval block Scale 5c8c7b72759e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L13-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall

theorem P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_blockScale_5c8c7b72759e {κ : Type} [Fintype κ] {n' : κ → ℕ} {A : Type*} [CommRing A]
    {f : MvPolynomial (Coord n') ℤ} {e : κ → ℕ} (hf : Geo.IsMultiHomog (ι := blockIdx n') f e)
    (c : κ → A) (v : Coord n' → A) :
    aeval (fun p ↦ c p.1 * v p) f = (∏ k, c k ^ e k) * aeval v f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSmall».«aeval_blockScale» := P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_blockScale_5c8c7b72759e
