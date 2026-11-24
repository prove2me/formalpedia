-- Prove2me | Theorems.Thm_SensitivityBaselineCheckpointRecipes_phase0_gate_eq
-- name    : SensitivityBaselineCheckpointRecipes.phase0_gate_eq
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:35:53.945591+00:00
-- url     : https://prove2.me/theorems/f34b6935-31f3-4838-9d3a-899ae0725abf
-- title:
--   Equivalence of the phase-zero unary gate recipes
-- statement:
--   Let $F$ be any colored child family with twelve ranks and let $\mathcal G$ be any family of unary guards. The gate built from the numerical phase-zero soft cutoffs, hard cutoffs, allowances, and target function is exactly the literal phase-zero gate:
--   $$
--   G(F,\mathcal G,\operatorname{unaryRecipe}(r_0))=G(F,\mathcal G,\operatorname{phase0Recipe}).
--   $$
--   The equality holds for every parent row, rank, and Boolean input.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineCheckpointRecipes.lean lines 18–31; SHA256 7e741d4ae4208a6c04ed4a40f50281fb1e15ef4139c69fb937b4464d7b072e72; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_CheckpointRankMapConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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

namespace SensitivityBaselineCheckpointRecipes
end SensitivityBaselineCheckpointRecipes
namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric
namespace SensitivityBaselineSourceCover
end SensitivityBaselineSourceCover
namespace SensitivityLocalNumericGateBridge
end SensitivityLocalNumericGateBridge
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


open SensitivityBaselineCheckpointRecipes
open SensitivityRankMapCheckpoint SensitivityRankedConstruction
open SensitivityBaselineLossNumeric SensitivityBaselineSourceCover
open SensitivityLocalNumericGateBridge
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem SensitivityBaselineCheckpointRecipes.phase0_gate_eq {V I Color : Type} (row : RowFamily I Color 12)
    (guards : GuardFamily V Unit) :
    gateRow row guards (unaryRecipe phase0.soft phase0.hard phase0.allowance phase0.lo) = gateRow row guards phase0Recipe := by sorry
