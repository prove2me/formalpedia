-- Prove2me | Theorems.Thm_SensitivityMacroPartitionModel_sum_clusterCounts
-- name    : SensitivityMacroPartitionModel.sum_clusterCounts
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:20.67477+00:00
-- url     : https://prove2.me/theorems/f0fef0cf-7537-44d6-b1a7-5ab8378e51ec
-- title:
--   Cluster counts sum once per guard macro
-- statement:
--   For any cluster map on Fin n, guard-index set G, and natural amount per cluster, the sum of clusterCounts over all indices equals the sum of those amounts over the image of G under the cluster map.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MacroPartitionCounts.lean lines 33–51; SHA256 2037b609f86a3cc25b982ede6311762781adf9ce5e7dc1b28204aa6a32027705; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionCounts
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

theorem SensitivityMacroPartitionModel.sum_clusterCounts (cluster : Fin n → M) (G : Finset (Fin n)) (amount : M → ℕ) :
    (∑ k, clusterCounts cluster G amount k) = ∑ m ∈ G.image cluster, amount m := by sorry
