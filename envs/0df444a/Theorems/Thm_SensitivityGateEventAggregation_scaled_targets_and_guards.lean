-- Prove2me | Theorems.Thm_SensitivityGateEventAggregation_scaled_targets_and_guards
-- name    : SensitivityGateEventAggregation.scaled_targets_and_guards
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:48.189308+00:00
-- url     : https://prove2.me/theorems/2a1dc9bf-930b-47f6-9889-078602288fee
-- title:
--   Summing scaled target and guard charges
-- statement:
--   Let $E$ be a finite set of bit coordinates, each lying either in a target socket of row $v$ or in one of its guard checks. Suppose the events in target side $s$ have cardinality at most $\sigma a_s$, and those lying in check $Q$ have cardinality at most $\sigma b_Q$. Then
--   $$
--   |E|\le\sigma\left(\sum_s a_s+\sum_{Q\in\mathcal G(v)}b_Q\right).
--   $$
--   The fees are natural numbers; overlaps among guard-supported event sets are harmless for this upper bound.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GateEventAggregation.lean lines 15–37; SHA256 2b789d437d944ed0a543c0e39154df06370145557fe83be53a19f8a9caa974e9; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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

theorem SensitivityGateEventAggregation.scaled_targets_and_guards {V S I : Type} [Fintype V] [Fintype S] [Fintype I]
    (E : Finset ((V × S) × I)) (guards : GuardFamily V S) (v : V)
    (hsupport : ∀ bit ∈ E, bit.1.1 = v ∨ ∃ check ∈ guards v, bit.1 ∈ check)
    (scale : ℝ) (ownFee : S → ℕ) (guardFee : Finset (V × S) → ℕ)
    (hown : ∀ s, (((Finset.univ : Finset I).filter fun i => ((v,s),i) ∈ E).card : ℝ) ≤ scale * ownFee s)
    (hguard : ∀ check ∈ guards v, ((E.filter fun bit => bit.1 ∈ check).card : ℝ) ≤ scale * guardFee check) :
    (E.card : ℝ) ≤ scale * ((∑ s : S, ownFee s) + ∑ check ∈ guards v, guardFee check : ℕ) := by sorry
