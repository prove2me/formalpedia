-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_4_1
-- name    : SparseDisc.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:12:37.012557+00:00
-- url     : https://prove2.me/theorems/03ac9705-43e5-4473-bd86-3e676b542702
-- title:
--   Theorem 4.1 — Berge-acyclic $t$-sparse instances
-- statement:
--   Let $t\ge1$. If $G=(g_v,U_v)_{v\in V}$ is a finite $t$-sparse instance whose bundle hypergraph is Berge-acyclic, then
--   $$
--   \operatorname{disc}(G)\le K_t.
--   $$
--   This is the instance-level theorem underlying Theorem 1.3 and retains declared supports that may strictly contain relevant coordinates.
--
--   Differences from the source:
--   - encoding: finite instance and bundle hypergraph → functions and items indexed by finite types, with declared support sparsity and acyclicity of the finite incidence graph; reason: Lean convention, preserving the paper's instance model
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 4.1, p.19

import Mathlib
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_InstDiscLE
import Definitions.Def_SparseDisc_Supplement_IsTSparseSupp
import Definitions.Def_SparseDisc_Supplement_BergeAcyclic
import Definitions.Def_SparseDisc_Supplement_K

namespace SparseDisc.Supplement

/-- **Theorem 4.1** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.19). Every Berge-acyclic `t`-sparse
instance has discrepancy at most `K t`.

**Formalization Note** Declared supports may strictly contain relevant coordinates. -/
theorem theorem_4_1 :
    ∀ (t : ℕ), 1 ≤ t → ∀ (V ι : Type) [Fintype V] [DecidableEq V]
      [Fintype ι] [DecidableEq ι] (g : V → SparseDisc.Cube ι → ℝ)
      (U : V → Finset ι), SparseDisc.IsInstance g U → IsTSparseSupp t U →
      BergeAcyclic U → SparseDisc.InstDiscLE g (K t) := by sorry

end SparseDisc.Supplement
