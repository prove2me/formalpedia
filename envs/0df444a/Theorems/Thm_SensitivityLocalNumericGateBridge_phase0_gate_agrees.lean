-- Prove2me | Theorems.Thm_SensitivityLocalNumericGateBridge_phase0_gate_agrees
-- name    : SensitivityLocalNumericGateBridge.phase0_gate_agrees
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:33.967922+00:00
-- url     : https://prove2.me/theorems/8f1130c0-2bbc-468c-b6fb-e0c4d81e41e6
-- title:
--   Strict-rank agreement of the phase-zero auxiliary recipe
-- statement:
--   For any twelve-rank child family and unary guards, the numerical recipe used in the phase-zero auxiliary recurrence agrees with the literal phase-zero gate at every rank $j\ge5$:
--   $$
--   G_{\mathrm{aux},v}(j,x)\iff G_{\mathrm{literal},v}(j,x).
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalNumericGateBridge.lean lines 104–117; SHA256 38ad83a478cce1add8f4e1dad1102b41ae3d86bb958a2139e7577a4ed21ca2e8; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_CheckpointRankMapConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericGateBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
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

namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalConfigurationCoverage
end SensitivityLocalConfigurationCoverage
namespace SensitivityLocalNumeric
end SensitivityLocalNumeric
namespace SensitivityLocalNumericGateBridge
end SensitivityLocalNumericGateBridge
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! The truncated numeric targets agree with the actual gates at every
strict rank. No equality of the loose-rank predicates is asserted. -/
open SensitivityLocalNumericGateBridge
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
variable {V S I Color : Type} {L core : ℕ}
open SensitivityLocalNumeric SensitivityRankMapCheckpoint SensitivityLocalConfigurationCoverage

theorem SensitivityLocalNumericGateBridge.phase0_gate_agrees (row : RowFamily I Color 12) (guards : GuardFamily V Unit) :
    AgreeAbove (gateRow row guards (unaryRecipe phase0.soft phase0.hard phase0Allowance phase0.lo))
      (gateRow row guards phase0Recipe) 5 := by sorry
