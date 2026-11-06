-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedLocalSharedBoundary_card_le
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.refinedLocalSharedBoundary_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:48:49.432686+00:00
-- url     : https://prove2.me/theorems/9d31773b-3590-4808-89a2-53ef4273b562
-- title:
--   Edge Restricted Stopped Recursion: refined Local Shared Boundary card le
-- statement:
--   The Edge Restricted Stopped Recursion construction uses the refined Local Shared Boundary card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Completion.lean#L328-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Completion.lean#L328-L340

import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.refinedLocalSharedBoundary_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    (edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile owner) ∩
      edgeDivisionSharedBoundary (tree.refinedEdgeRegion beta exponent hProfile)
        (tree.refinedEdgeActive beta exponent hProfile)).card ≤
      6 * weightedSpineSeparatorBudget beta exponent r := by sorry
