-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exists_form_notMem_9e34f112a8d3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_exists_form_notMem_9e34f112a8d3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:59.933669+00:00
-- url     : https://prove2.me/theorems/0797a636-97d1-4ada-ab9e-84d3a855fc53
-- title:
--   P2 M Ground Theory Heights  Heights Inter exists form not Mem 9e34f112a8d3: P2 M Ground Theory Heights  Heights Inter exists form not Mem 9e34f112a8d3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter exists form not Mem 9e34f112a8d3 construction uses the P2 M Ground Theory Heights  Heights Inter exists form not Mem 9e34f112a8d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocRing.lean#L180-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocRing.lean#L180-L185

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem P2M_GroundTheory_Heights__Heights_Inter_exists_form_notMem_9e34f112a8d3 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {W : Ideal (MRing ι)}
    (hW : IsRelevant W) (hWp : W.IsPrime) (α : K → ℕ) : ∃ t : MRing ι, IsMultiHomog t α ∧ t ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«exists_form_notMem» := P2M_GroundTheory_Heights__Heights_Inter_exists_form_notMem_9e34f112a8d3
