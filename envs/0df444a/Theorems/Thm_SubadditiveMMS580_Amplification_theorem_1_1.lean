-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_theorem_1_1
-- name    : SubadditiveMMS580.Amplification.theorem_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T19:54:24.484799+00:00
-- url     : https://prove2.me/theorems/50414bec-b3e0-48e4-a26a-abea5bd1506a
-- title:
--   Theorem 1.1 — every subadditive instance admits an $\alpha(n)$-MMS allocation, $\alpha(n)=1/(4D(n)-2)>1/(8(1+\log_2^* n))$
-- statement:
--   Let $n\ge2$ agents have valuations $v_1,\dots,v_n:2^M\to\mathbb R$ on an arbitrary finite set of goods $M$ that are normalized ($v_i(\varnothing)=0$), monotone ($S\subseteq T\Rightarrow v_i(S)\le v_i(T)$) and subadditive ($v_i(S\cup T)\le v_i(S)+v_i(T)$ for all $S,T$). Let $\mu_i=\operatorname{MMS}_n(v_i;M)$ be agent $i$'s maximin share: the maximum, over all ordered partitions of $M$ into $n$ possibly empty bundles, of the least value of a bundle. Define
--   $$E_0=1,\ E_{r+1}=2^{E_r},\quad \log_2^*n=\min\{r\ge0:n\le E_r\},\quad d(n)=1+\log_2^* n,\quad D(n)=2^{\lceil\log_2 d(n)\rceil},\quad \alpha(n)=\frac1{4D(n)-2},$$
--   so $D(n)$ is the smallest power of two at least $d(n)$. Then there are pairwise disjoint bundles $A_1,\dots,A_n\subseteq M$ such that
--   $$v_i(A_i)\ \ge\ \alpha(n)\,\mu_i\qquad\text{for every agent } i,$$
--   and in particular
--   $$\alpha(n)\ >\ \frac{1}{8\,(1+\log_2^* n)} .$$
--
--   This improves the best known general maximin-share guarantee for subadditive valuations from $\Omega(1/\log\log n)$ to $\Omega(1/\log^* n)$; the factor depends only on the number of agents, not on the number of goods or the valuations.
--
--   **Formalization Note** Goods are `Fin m` for an arbitrary $m\ge0$, agents `Fin n`. The bundles form a partial allocation; by monotonicity it can be completed without lowering any value. Agents with $\mu_i=0$ and instances with $m<n$ (including $m=0$) are included; their target is then $0$. $\operatorname{MMS}$ is the published `LittleCharity.MMS.mms` (a maximum over all labellings of the goods by $[n]$; only the definition of `mms` from that file is used, not its additivity predicate). $\log_2^*$, $D$ and $\alpha$ are the definitions of this mission, with $\lceil\log_2 d\rceil$ computed as the least $k$ with $d\le2^k$.
--
--   Differences from the source:
--   - encoding: goods $M$, agents $[n]$ → `Fin m`, `Fin n`; reason: relabelling; every finite instance is covered.
--   - encoding: valuations $v:2^M\to\mathbb R_{\ge0}$ → real-valued set functions with `IsNormalized` and `IsMonotone`; reason: normalization and monotonicity give $v(S)\ge v(\varnothing)=0$, so exactly the same valuations.
-- source:
--   Bo Li, Ankang Sun, STOC 2027 submission #580 (October 2026), Theorem 1.1 with the definitions of d(n), D(n), α(n), p. 2; eq. (2), p. 8; proof §3.4, pp. 19–20

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification

/-- Theorem 1.1 (General subadditive valuations; Li–Sun, STOC 2027 submission #580, p. 2): every
instance with `n ≥ 2` agents and normalized monotone subadditive valuations on finitely many goods
`Fin m` admits an `α(n)`-MMS allocation, `α(n) = 1/(4D(n) − 2)`: pairwise disjoint bundles `A_i`
with `v_i(A_i) ≥ α(n) · MMS_n(v_i; M)`. In particular `α(n) > 1/(8(1 + log*₂ n))`. -/
theorem theorem_1_1 (n : ℕ) (hn : 2 ≤ n) {m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) :
    (∃ A : Fin n → Finset (Fin m), IsAllocation A ∧
      ∀ i : Fin n, alpha n * LittleCharity.MMS.mms (v i) n Finset.univ ≤ v i (A i)) ∧
    1 / (8 * (1 + (logStar n : ℝ))) < alpha n := by sorry

end SubadditiveMMS580.Amplification
