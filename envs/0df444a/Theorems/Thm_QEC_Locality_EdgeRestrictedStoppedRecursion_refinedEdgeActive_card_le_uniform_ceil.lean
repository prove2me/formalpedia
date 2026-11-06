-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedEdgeActive_card_le_uniform_ceil
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeActive_card_le_uniform_ceil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:49:52.051595+00:00
-- url     : https://prove2.me/theorems/cbfc0d80-f243-4843-a337-4229f602fb0d
-- title:
--   Edge Restricted Stopped Recursion: refined Edge Active card le uniform ceil
-- statement:
--   Exact graph-uniform ceiling form of the two-phase active-region count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedPotential.lean#L722-L740
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedPotential.lean#L722-L740

import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeActive_card_le_uniform_ceil
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 1 ≤ r) (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hlower : r ≤ 4 * vertices.card) :
    (tree.refinedEdgeActive beta exponent hProfile).card ≤
      Nat.ceil (profileDivisionRegionConstant beta exponent * vertices.card / r) := by sorry
