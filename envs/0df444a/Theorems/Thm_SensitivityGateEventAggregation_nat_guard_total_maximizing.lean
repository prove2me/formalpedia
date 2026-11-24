-- Prove2me | Theorems.Thm_SensitivityGateEventAggregation_nat_guard_total_maximizing
-- name    : SensitivityGateEventAggregation.nat_guard_total_maximizing
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:17.086806+00:00
-- url     : https://prove2.me/theorems/539f29e6-eacf-4943-a76c-6d2f191fb4b2
-- title:
--   Maximizing one-or-two guard slots dominates every actual allocation
-- statement:
--   Let each occupied guard use one or two slots, with total slots at most D and twice the occupied-guard count at most D. For nonnegative integer baseline, combined, and upward fees, the cost (D−total slots)·baseline plus the occupied combined and extra-slot fees is at most the cost obtained by choosing maximizingNatSlots separately for each guard.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/GateEventAggregation.lean lines 100–123; SHA256 2b789d437d944ed0a543c0e39154df06370145557fe83be53a19f8a9caa974e9; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_GateEventAggregation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGateEventAggregation
end SensitivityGateEventAggregation
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityGuardFeeAggregation
end SensitivityGuardFeeAggregation
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityPairedGuardNumericSlices
end SensitivityPairedGuardNumericSlices
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport


/-! Summing exact own-socket and guard slices, with physical guard slots. -/
open SensitivityGateEventAggregation
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityFiniteRanks SensitivityGuardEvents SensitivitySocketEventSupport
open SensitivityLocalNumericSemantics SensitivityPairedGuardNumericSlices
open SensitivityGuardFeeAggregation
set_option autoImplicit false

theorem SensitivityGateEventAggregation.nat_guard_total_maximizing {G : Type} (occupied : Finset G) (slots : G → ℕ)
    (D : ℕ) (combined upward : G → ℕ) (baseline : ℕ)
    (hrange : ∀ check ∈ occupied, 1 ≤ slots check ∧ slots check ≤ 2)
    (hactual : (∑ check ∈ occupied, slots check) ≤ D)
    (hroom : occupied.card * 2 ≤ D) :
    (((D - ∑ check ∈ occupied, slots check) * baseline +
        ∑ check ∈ occupied, (combined check + (slots check-1) * upward check) : ℕ) : ℝ) ≤
      (((D - ∑ check ∈ occupied, maximizingNatSlots baseline (upward check)) * baseline +
        ∑ check ∈ occupied, (combined check +
          (maximizingNatSlots baseline (upward check)-1)*upward check) : ℕ) : ℝ) := by sorry
