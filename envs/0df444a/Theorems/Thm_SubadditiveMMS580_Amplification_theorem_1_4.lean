-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_theorem_1_4
-- name    : SubadditiveMMS580.Amplification.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:54:24.75383+00:00
-- url     : https://prove2.me/theorems/440cfc06-1de3-4d9d-b12e-4d4ba24febfc
-- title:
--   Theorem 1.4 — amplification from disjoint valuable bundles
-- statement:
--   Let $u\ge2$ and $n\ge1$ be integers. Suppose each of $u$ agents has a valuation $v_i:2^M\to\mathbb R$ on a finite set of goods $M$ that is normalized ($v_i(\varnothing)=0$), monotone and subadditive, together with $n$ pairwise disjoint sets $W_{i,1},\dots,W_{i,n}\subseteq M$ of value $v_i(W_{i,r})\ge1$. Here $n$ counts the valuable sets available to each agent and need not equal $u$. Then for every integer $\ell\ge1$ with $2\ell(u-1)\le n$:
--
--   1. there is a finitely supported distribution over feasible allocations $(A_i)_{i\in[u]}$ (pairwise disjoint bundles) such that, for each agent $i$,
--   $$\Pr\bigl[v_i(A_i)<\tfrac12\bigr]\ \le\ \Bigl(\frac12+\frac{\ell(u-1)}{n}\Bigr)^{\ell};$$
--   2. if moreover $n\ge4\ell(u-1)$, there is a feasible partial allocation $(A_i)_{i\in[u]}$ in which at most $\lfloor u(3/4)^{\ell}\rfloor$ agents receive value below $1/2$.
--
--   One distribution serves all agents simultaneously, and in part 2 one allocation serves all the successful agents together. Part 2 is what Proposition 3.4 uses to build the amplified layers: the number of unserved agents drops exponentially in the number $\ell$ of trials.
--
--   **Formalization Note** Goods are `Fin m`, agents `Fin u`, set indices `Fin n`. All fractions are computed in $\mathbb R$; $u-1$ in the natural-number hypotheses is safe because $u\ge2$. The floor is the natural-number floor of the nonnegative real $u(3/4)^\ell$.
--
--   Differences from the source:
--   - encoding: goods $M$, agents $[u]$, indices $[n]$ → `Fin m`, `Fin u`, `Fin n`; reason: relabelling; every finite instance is covered.
--   - encoding: valuations $v:2^M\to\mathbb R_{\ge0}$ → real-valued set functions with `IsNormalized` and `IsMonotone`; reason: normalization and monotonicity give $v(S)\ge v(\varnothing)=0$, so exactly the same valuations.
--   - encoding: finitely supported distribution $\sigma$ and $\Pr_\sigma$ → `FinDist` (finite support, positive weights summing to $1$) and `FinDist.prob` (total weight of the support points where the event holds); reason: the same objects; no measure theory needed for finite support.
-- source:
--   Bo Li, Ankang Sun, STOC 2027 submission #580 (October 2026), Theorem 1.4, p. 5 (proof §3.2, pp. 13–16)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification

/-- Theorem 1.4 (Amplification from disjoint valuable bundles; Li–Sun, STOC 2027 submission #580,
p. 5): let `u ≥ 2`, `n ≥ 1`; `u` agents with normalized monotone subadditive valuations on
`Fin m`, each having `n` pairwise disjoint sets of value at least one. For every integer `ℓ ≥ 1`
with `2ℓ(u−1) ≤ n` there is a finitely supported distribution over feasible allocations with
`P[v_i(A_i) < 1/2] ≤ (1/2 + ℓ(u−1)/n)^ℓ` for each agent `i`; and if `n ≥ 4ℓ(u−1)`, some feasible
partial allocation leaves at most `⌊u (3/4)^ℓ⌋` agents below value `1/2`. -/
theorem theorem_1_4 (u n : ℕ) (hu : 2 ≤ u) (hn : 1 ≤ n) {m : ℕ}
    (v : Fin u → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (W : Fin u → Fin n → Finset (Fin m)) (hW : ∀ i, IsValuableFamily (v i) (W i))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : 2 * ℓ * (u - 1) ≤ n) :
    (∃ σ : FinDist (Fin u → Finset (Fin m)),
      (∀ A ∈ σ.support, IsAllocation A) ∧
      ∀ i : Fin u, σ.prob (fun A => v i (A i) < 1 / 2) ≤
        ((1 : ℝ) / 2 + (ℓ : ℝ) * ((u : ℝ) - 1) / (n : ℝ)) ^ ℓ) ∧
    (4 * ℓ * (u - 1) ≤ n →
      ∃ A : Fin u → Finset (Fin m), IsAllocation A ∧
        (Finset.univ.filter (fun i => v i (A i) < 1 / 2)).card ≤
          ⌊(u : ℝ) * ((3 : ℝ) / 4) ^ ℓ⌋₊) := by sorry

end SubadditiveMMS580.Amplification
