-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_corollary_3_3
-- name    : SubadditiveMMS580.Amplification.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:54:26.464227+00:00
-- url     : https://prove2.me/theorems/ff4e8aeb-7d5d-4b75-bbf4-3b3492293883
-- title:
--   Corollary 3.3 — half-value partial allocation from $n$ disjoint valuable sets per agent
-- statement:
--   Let $1\le u\le n$. Suppose $u$ agents have normalized, monotone, subadditive valuations $v_1,\dots,v_u:2^M\to\mathbb R$ on a finite set of goods $M$, and each agent $i\in[u]$ has $n$ pairwise disjoint sets $W_{i,1},\dots,W_{i,n}\subseteq M$ with
--   $$v_i(W_{i,r})\ge1\qquad\text{for every } r\in[n].$$
--   (Disjointness is required only within one agent's family; families of different agents may overlap, and no family need cover $M$.) Let $k=\lfloor n/u\rfloor$. Then there exists a feasible partial allocation $(A_i)_{i\in[u]}$ such that
--   $$\bigl|\{\,i\in[u]:\ v_i(A_i)\ge\tfrac12\,\}\bigr|\ \ge\ \frac{u\,k}{k+1}.$$
--
--   This turns Lemma 3.2 into a statement about agents who only know $n$ disjoint valuable sets, which is the invariant maintained for the unserved agents across the layers of Proposition 3.4.
--
--   **Formalization Note** Goods are `Fin m`, agents `Fin u`, set indices `Fin n`. The served count is compared with the real number $uk/(k+1)$ after casting; $k$ is natural-number division $\lfloor n/u\rfloor$.
--
--   Differences from the source:
--   - encoding: goods $M$, agents $[u]$, indices $r\in[n]$ → `Fin m`, `Fin u`, `Fin n`; reason: relabelling; every finite instance is covered.
--   - encoding: valuations $v:2^M\to\mathbb R_{\ge0}$ → real-valued set functions with `IsNormalized` and `IsMonotone`; reason: normalization and monotonicity give $v(S)\ge v(\varnothing)=0$, so exactly the same valuations.
-- source:
--   Bo Li, Ankang Sun, STOC 2027 submission #580 (October 2026), Corollary 3.3, p. 16

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification

/-- Corollary 3.3 (Li–Sun, STOC 2027 submission #580, p. 16): let `1 ≤ u ≤ n`; `u` agents with
normalized monotone subadditive valuations on `Fin m`, each agent `i` having `n` pairwise
disjoint sets `W i 1, …, W i n` with `v_i(W i r) ≥ 1`. Then some feasible partial allocation
gives value at least `1/2` to at least `uk/(k+1)` agents, where `k = ⌊n/u⌋`. -/
theorem corollary_3_3 (u n : ℕ) (hu : 1 ≤ u) (hun : u ≤ n) {m : ℕ}
    (v : Fin u → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (W : Fin u → Fin n → Finset (Fin m)) (hW : ∀ i, IsValuableFamily (v i) (W i)) :
    ∃ A : Fin u → Finset (Fin m), IsAllocation A ∧
      (u : ℝ) * ((n / u : ℕ) : ℝ) / (((n / u : ℕ) : ℝ) + 1) ≤
        ((Finset.univ.filter (fun i => (1 : ℝ) / 2 ≤ v i (A i))).card : ℝ) := by sorry

end SubadditiveMMS580.Amplification
