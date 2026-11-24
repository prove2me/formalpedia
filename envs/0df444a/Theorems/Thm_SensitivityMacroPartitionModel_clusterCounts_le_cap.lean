-- Prove2me | Theorems.Thm_SensitivityMacroPartitionModel_clusterCounts_le_cap
-- name    : SensitivityMacroPartitionModel.clusterCounts_le_cap
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:24.933506+00:00
-- url     : https://prove2.me/theorems/73425232-13ee-4b12-9bce-4d6a71d17035
-- title:
--   Per-member residual bounds imply the representative group cap
-- statement:
--   If a cluster's assigned amount is at most every member's residual, then every representative clusterCount is bounded by groupCap for the representative partition and those residuals.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MacroPartitionCounts.lean lines 63–81; SHA256 2037b609f86a3cc25b982ede6311762781adf9ce5e7dc1b28204aa6a32027705; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionCounts
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace SensitivityMacroPartitionModel
end SensitivityMacroPartitionModel


/-! The counts attached to a cluster are kept once for pricing and once per
guard head for the uncompressed incidence budget. The finite product of
bounded counts includes every actual assignment. -/
open SensitivityMacroPartitionModel
open scoped Classical BigOperators
set_option autoImplicit false
variable {n : ℕ} {M : Type}

theorem SensitivityMacroPartitionModel.clusterCounts_le_cap (cluster : Fin n → M) (G : Finset (Fin n)) (amount : M → ℕ)
    (residual : Fin n → ℕ) (hbound : ∀ i, amount (cluster i) ≤ residual i) (k : Fin n) :
    clusterCounts cluster G amount k ≤ groupCap (representative cluster) residual k := by sorry
