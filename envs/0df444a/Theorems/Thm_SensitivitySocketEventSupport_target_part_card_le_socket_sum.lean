-- Prove2me | Theorems.Thm_SensitivitySocketEventSupport_target_part_card_le_socket_sum
-- name    : SensitivitySocketEventSupport.target_part_card_le_socket_sum
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:32.224852+00:00
-- url     : https://prove2.me/theorems/deb01bc0-d7c1-4e5a-9adf-949565127334
-- title:
--   Bounding a target-supported event set by its socket slices
-- statement:
--   For any finite coordinate set $E$ and parent row $v$,
--   $$
--   |\{b\in E:\operatorname{row}(b)=v\}|
--   \le\sum_{s\in S}|\{i:((v,s),i)\in E\}|.
--   $$
--   The side set and child-coordinate set are finite.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/SocketEventSupport.lean lines 121–135; SHA256 130fe497348703de4239bb018f369361b0f106607f6b96d96ba8a7df66968208; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates


/-! Actual one-bit support and decomposition of local gate events. -/
open SensitivitySocketEventSupport
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
set_option autoImplicit false
variable {V S I Color : Type} {L : ℕ}

theorem SensitivitySocketEventSupport.target_part_card_le_socket_sum [Fintype S] [Fintype I]
    (E : Finset ((V × S) × I)) (v : V) :
    (E.filter fun bit => bit.1.1 = v).card ≤
      ∑ s : S, ((Finset.univ : Finset I).filter fun i => ((v,s),i) ∈ E).card := by sorry
