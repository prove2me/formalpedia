-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_subfield_closure_coords_eq_top_76055511fe92
-- name    : P2M_GroundTheory_Heights__Heights_Inter_subfield_closure_coords_eq_top_76055511fe92
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:32:34.263131+00:00
-- url     : https://prove2.me/theorems/7338d0fa-d3ac-48d3-848e-0858efd1f49e
-- title:
--   P2 M Ground Theory Heights  Heights Inter subfield closure coords eq top 76055511fe92: P2 M Ground Theory Heights  Heights Inter subfield closure coords eq top 76055511fe92
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter subfield closure coords eq top 76055511fe92 construction uses the P2 M Ground Theory Heights  Heights Inter subfield closure coords eq top 76055511fe92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingIntClosure.lean#L15-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingIntClosure.lean#L15-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingIntClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingChartLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StIntClosureLocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingIntClosure
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
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_subfield_closure_coords_eq_top_76055511fe92 {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι')) [P'.IsPrime] :
    Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
        Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«subfield_closure_coords_eq_top» := P2M_GroundTheory_Heights__Heights_Inter_subfield_closure_coords_eq_top_76055511fe92
