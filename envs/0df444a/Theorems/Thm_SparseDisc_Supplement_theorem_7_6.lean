-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_7_6
-- name    : SparseDisc.Supplement.theorem_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:13:42.522555+00:00
-- url     : https://prove2.me/theorems/512c17b2-ec5e-44b4-85fa-f7b68ce1a027
-- title:
--   Theorem 7.6 — bounded ports for heavy instance functions
-- statement:
--   Let $\Delta\ge2$ and $C=t\Delta\max(1,2^{\Delta-2})$. If $G$ is a finite $t$-sparse instance in which every heavy function has at most $\Delta$ ports in each lobe, then
--   $$
--   \operatorname{disc}(G)\le C.
--   $$
--   The statement is at instance level and therefore allows declared supports larger than the relevant-coordinate sets.
--
--   Differences from the source:
--   - encoding: lobes and ports in the bundle hypergraph → reflexive-transitive hyperedge co-membership after deletion and a finite port count; reason: direct encoding of Definition 7.1
--   - encoding: finite $t$-sparse instance → finite function and item types with the published `IsInstance` predicate and general declared-support sparsity; reason: Lean convention, preserving nonminimal supports
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 7.6, p.27

import Mathlib
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_InstDiscLE
import Definitions.Def_SparseDisc_Supplement_IsTSparseSupp
import Definitions.Def_SparseDisc_Supplement_PortCondition

namespace SparseDisc.Supplement

/-- **Theorem 7.6** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.27). A `t`-sparse instance whose heavy
functions have at most `Δ` ports in every lobe has discrepancy at most
`tΔ max(1,2^(Δ-2))`. -/
theorem theorem_7_6 :
    ∀ (t Δ : ℕ), 1 ≤ t → 2 ≤ Δ → ∀ (V ι : Type) [Fintype V]
      [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (g : V → SparseDisc.Cube ι → ℝ) (U : V → Finset ι),
      SparseDisc.IsInstance g U → IsTSparseSupp t U → PortCondition U Δ →
      SparseDisc.InstDiscLE g ((t * Δ * max 1 (2 ^ (Δ - 2)) : ℕ) : ℝ) := by sorry

end SparseDisc.Supplement
