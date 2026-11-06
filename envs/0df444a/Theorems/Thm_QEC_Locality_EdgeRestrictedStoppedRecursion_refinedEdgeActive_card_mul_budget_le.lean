-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedEdgeActive_card_mul_budget_le
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeActive_card_mul_budget_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:48:13.201472+00:00
-- url     : https://prove2.me/theorems/78a1a6ef-a4e7-4735-afd0-1393e20d9a5d
-- title:
--   Edge Restricted Stopped Recursion: refined Edge Active card mul budget le
-- statement:
--   The Edge Restricted Stopped Recursion construction uses the refined Edge Active card mul budget le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Completion.lean#L385-L399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Completion.lean#L385-L399

import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeActive_card_mul_budget_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    (tree.refinedEdgeActive beta exponent hProfile).card *
        weightedSpineSeparatorBudget beta exponent r ≤
      tree.terminalOwnerCount * weightedSpineSeparatorBudget beta exponent r +
        2 * tree.terminalBoundaryMass := by sorry
