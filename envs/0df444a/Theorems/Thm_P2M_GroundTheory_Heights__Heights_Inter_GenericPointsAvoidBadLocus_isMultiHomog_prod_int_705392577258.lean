-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_GenericPointsAvoidBadLocus_isMultiHomog_prod_int_705392577258
-- name    : P2M_GroundTheory_Heights__Heights_Inter_GenericPointsAvoidBadLocus_isMultiHomog_prod_int_705392577258
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:30.821572+00:00
-- url     : https://prove2.me/theorems/a6947f8d-d23f-51c4-b731-f85b997fc15f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Generic Points Avoid Bad Locus is Multi Homog prod int 705392577258: P2 M Ground Theory Heights  Heights Inter Generic Points Avoid Bad Locus is Multi Homog p
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Generic Points Avoid Bad Locus is Multi Homog prod int 705392577258 construction uses the P2 M Ground Theory Heights  Heights Inter Generic Points Avoid Bad Locus is Multi Homog prod int 705392577258 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogProdInt.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogProdInt.lean#L18-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogProdInt
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Inter_GenericPointsAvoidBadLocus_isMultiHomog_prod_int_705392577258 {β : Type*} (s : Finset β) (f : β → MRing ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«GenericPointsAvoidBadLocus».«isMultiHomog_prod_int» := P2M_GroundTheory_Heights__Heights_Inter_GenericPointsAvoidBadLocus_isMultiHomog_prod_int_705392577258
