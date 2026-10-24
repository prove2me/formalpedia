-- Prove2me | Theorems.Thm_ProjRescale_MaxSupport_partition_claim
-- name    : ProjRescale.MaxSupport.partition_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:31.968157+00:00
-- url     : https://prove2.me/theorems/db6c59c5-3592-4d4a-9540-35391200140f
-- title:
--   §2, p. 4 — partition claim: J(L) and J(L⊥) partition {1, …, n}
-- statement:
--   Let $L \subseteq \mathbb R^n$ be a linear subspace with orthogonal complement $L^\perp$, and let $J(L) = \{j : x_j > 0 \text{ for some } x \in L \cap \mathbb R^n_+\}$ be its maximum support index set. Then the maximum support index sets of $L$ and $L^\perp$ partition $\{1,\dots,n\}$:
--
--   $$J(L) \cap J(L^\perp) = \emptyset \quad\text{and}\quad J(L) \cup J(L^\perp) = \{1,\dots,n\}.$$
--
--   This is the duality fact behind Algorithm 2: it makes the covering condition $J \cup \hat J = \{1,\dots,n\}$ a certificate that both index sets are maximal (Corollary 1).
--
--   Differences from the source: none.
-- source:
--   Peña & Soheili, Projection and rescaling algorithm for finding maximum support solutions to polyhedral conic systems, arXiv:2003.08911v3, p. 4, §2 (unnumbered claim after the definition of σ(L))

import Mathlib
import Definitions.Def_ProjRescale_MaxSupport_Setting

namespace ProjRescale.MaxSupport

/-- §2, p. 4: the maximum support index sets `J(L)` and `J(L⊥)` partition `{1, …, n}`. -/
theorem partition_claim {n : ℕ} (L : Submodule ℝ (E n)) :
    maxSupp L ∩ maxSupp Lᗮ = ∅ ∧ maxSupp L ∪ maxSupp Lᗮ = Finset.univ := by sorry

end ProjRescale.MaxSupport
