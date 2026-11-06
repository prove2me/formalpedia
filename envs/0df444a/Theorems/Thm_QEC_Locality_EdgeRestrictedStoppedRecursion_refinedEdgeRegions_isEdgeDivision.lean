-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedEdgeRegions_isEdgeDivision
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeRegions_isEdgeDivision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:48:21.139029+00:00
-- url     : https://prove2.me/theorems/cd5f9c60-1405-481b-8ef0-00eedceefd0f
-- title:
--   Edge Restricted Stopped Recursion: refined Edge Regions is Edge Division
-- statement:
--   The Edge Restricted Stopped Recursion construction uses the refined Edge Regions is Edge Division property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Completion.lean#L192-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Completion.lean#L192-L214

import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeRegions_isEdgeDivision
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hroot : edges = directedEdgeFinset G) :
    IsEdgeDivision G (tree.refinedEdgeRegion beta exponent hProfile)
      (tree.refinedEdgeActive beta exponent hProfile) := by sorry
