-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_5_2
-- name    : SparseDisc.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:13:12.226703+00:00
-- url     : https://prove2.me/theorems/b97216ee-14cd-4b8c-bfb9-3127f0307d19
-- title:
--   Theorem 5.2 — arbitrary bundle structures
-- statement:
--   Let $G=(g_v,U_v)_{v\in V}$ be an instance with bundle structure $(B_e,S_e)_{e\in E}$, and suppose $d_v=|\{e:v\in S_e\}|\ge1$. Put
--   $$
--   k_e=\sum_{v\in S_e}\max(1,2^{d_v-2}).
--   $$
--   Then there is a sign colouring $x$ satisfying
--   $$
--   |g_v(x)|\le\sum_{e\in N(v)}\min(k_e,|B_e|)\qquad\text{for every }v.
--   $$
--   In particular, if the structure is $t$-bounded and $d_v\le\Delta$ for every $v$, then $\operatorname{disc}(G)\le t\Delta\max(1,2^{\Delta-2})$.
--
--   Differences from the source:
--   - encoding: finite bundle structure $(B_e,S_e)$ → finite index types and `Finset` bundles with nonemptiness, pairwise disjointness and support coverage stated in `IsBundleStructure`; reason: Lean convention, matching Definition 5.1 clause by clause
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 5.2, p.21

import Mathlib
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_InstDiscLE
import Definitions.Def_SparseDisc_Supplement_IsBundleStructure

namespace SparseDisc.Supplement

open Classical in
/-- **Theorem 5.2** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.21). For an arbitrary bundle structure,
there is one colouring satisfying every per-function sum of `min(k_e,|B_e|)`; the exact
`tΔ max(1,2^(Δ-2))` consequence is included. -/
theorem theorem_5_2 :
    ∀ (V ι E : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      [Fintype E] [DecidableEq E] (g : V → SparseDisc.Cube ι → ℝ)
      (U : V → Finset ι) (B : E → Finset ι) (S : E → Finset V),
      SparseDisc.IsInstance g U → IsBundleStructure U B S →
      let N := fun v => Finset.univ.filter (fun e => v ∈ S e)
      let d := fun v => (N v).card
      let k := fun e => ∑ v ∈ S e, max 1 (2 ^ (d v - 2))
      (∀ v, 1 ≤ d v) →
      (∃ x : SparseDisc.Cube ι, ∀ v,
        |g v x| ≤ ((∑ e ∈ N v, min (k e) (B e).card : ℕ) : ℝ)) ∧
      ∀ (t Δ : ℕ), (∀ e, (S e).card ≤ t) → (∀ v, d v ≤ Δ) →
        SparseDisc.InstDiscLE g ((t * Δ * max 1 (2 ^ (Δ - 2)) : ℕ) : ℝ) := by sorry

end SparseDisc.Supplement
