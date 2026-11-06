-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedEdgeRegion_incident_card_le
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeRegion_incident_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:47:57.768202+00:00
-- url     : https://prove2.me/theorems/f95b945f-8d93-48c0-a667-05117c956171
-- title:
--   Edge Restricted Stopped Recursion: refined Edge Region incident card le
-- statement:
--   The Edge Restricted Stopped Recursion construction uses the refined Edge Region incident card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Completion.lean#L158-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Completion.lean#L158-L165

import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeRegion_incident_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    (edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile owner)).card ≤ r := by sorry
