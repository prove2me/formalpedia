-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_proposition_3_4
-- name    : SubadditiveMMS580.Amplification.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:54:33.822099+00:00
-- url     : https://prove2.me/theorems/c04c6a75-a387-43fc-9380-e8a1f0e208cb
-- title:
--   Proposition 3.4 — a half-value multi-allocation with multiplicity at most $1+\log_2^* n$
-- statement:
--   Suppose $n\ge2$ agents have normalized, monotone, subadditive valuations $v_1,\dots,v_n:2^M\to\mathbb R$ on a finite set of goods $M$, and each agent $i\in[n]$ has $n$ pairwise disjoint sets $W_{i,1},\dots,W_{i,n}\subseteq M$ with $v_i(W_{i,r})\ge1$ for every $r\in[n]$. Then there exists a multi-allocation $(B_i)_{i\in[n]}$ — bundles that may overlap — such that
--   $$v_i(B_i)\ge\tfrac12\quad\text{for every agent } i,\qquad\text{and every good lies in at most } 1+\log_2^* n \text{ of the bundles},$$
--   where $\log_2^* n=\min\{r\ge0: n\le E_r\}$ with $E_0=1$, $E_{r+1}=2^{E_r}$ (equation (2)).
--
--   Combined with Feige's rounding theorem (Theorem 2.3) at $D=D(n)$, this multiplicity bound yields the factor $\alpha(n)$ of Theorem 1.1.
--
--   **Formalization Note** Goods are `Fin m`, agents and set indices `Fin n`. "Multiplicity at most $d$" is the published `IsMultiAllocation d`: every good belongs to at most $d$ bundles. There is no assumption on singleton values and the families need not cover $M$.
--
--   Differences from the source:
--   - encoding: goods $M$, agents $[n]$, indices $[n]$ → `Fin m`, `Fin n`, `Fin n`; reason: relabelling; every finite instance is covered.
--   - encoding: valuations $v:2^M\to\mathbb R_{\ge0}$ → real-valued set functions with `IsNormalized` and `IsMonotone`; reason: normalization and monotonicity give $v(S)\ge v(\varnothing)=0$, so exactly the same valuations.
-- source:
--   Bo Li, Ankang Sun, STOC 2027 submission #580 (October 2026), Proposition 3.4, p. 17 (proof pp. 17–19; log*₂ from eq. (2), p. 8)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification

/-- Proposition 3.4 (Few allocation layers; Li–Sun, STOC 2027 submission #580, p. 17): `n ≥ 2`
agents with normalized monotone subadditive valuations on `Fin m`, each agent `i` having `n`
pairwise disjoint sets `W i 1, …, W i n` with `v_i(W i r) ≥ 1`. Then there is a multi-allocation
`(B_i)` with `v_i(B_i) ≥ 1/2` for every agent and multiplicity at most `1 + log*₂ n`. -/
theorem proposition_3_4 (n : ℕ) (hn : 2 ≤ n) {m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (W : Fin n → Fin n → Finset (Fin m)) (hW : ∀ i, IsValuableFamily (v i) (W i)) :
    ∃ B : Fin n → Finset (Fin m), IsMultiAllocation (1 + logStar n) B ∧
      ∀ i : Fin n, (1 : ℝ) / 2 ≤ v i (B i) := by sorry

end SubadditiveMMS580.Amplification
