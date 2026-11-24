-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_semiToLoc_coe_6afe5d0b143c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_semiToLoc_coe_6afe5d0b143c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:40.739288+00:00
-- url     : https://prove2.me/theorems/331f677a-ede4-460c-acde-5d3528048b64
-- title:
--   P2 M Ground Theory Heights  Heights Inter semi To Loc coe 6afe5d0b143c: P2 M Ground Theory Heights  Heights Inter semi To Loc coe 6afe5d0b143c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter semi To Loc coe 6afe5d0b143c construction uses the P2 M Ground Theory Heights  Heights Inter semi To Loc coe 6afe5d0b143c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocMaxIdeals.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocMaxIdeals.lean#L27-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreIncomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_semiToLoc_coe_6afe5d0b143c (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    (b : semiLocRing P 𝒲) : ((semiToLoc P 𝒲 W hW b : locRing P W) : FractionRing (MRing ι ⧸ P)) = b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«semiToLoc_coe» := P2M_GroundTheory_Heights__Heights_Inter_semiToLoc_coe_6afe5d0b143c
