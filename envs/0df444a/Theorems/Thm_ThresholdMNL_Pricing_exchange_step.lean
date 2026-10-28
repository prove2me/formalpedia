-- Prove2me | Theorems.Thm_ThresholdMNL_Pricing_exchange_step
-- name    : ThresholdMNL.Pricing.exchange_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:18.289385+00:00
-- url     : https://prove2.me/theorems/498e8ff7-f828-4f8e-adb4-fd0ea5300ee3
-- title:
--   OS p. 1 (PDF 34), proof of Theorem 2, first claim — swapping two products' nominal utilities by the markups m′_j, m′_k keeps the attractiveness and strictly raises profit
-- statement:
--   Work in the TMNL model with $\beta>0$ and $\Delta\ge0$. Let $S$ be an offer set, $p$ a price vector with markups $m_i=p_i-c_i$ and nominal utilities $u_i=\hat\alpha_i-\beta m_i$, where $\hat\alpha_i=\alpha_i-\beta c_i$. Let $j,k\in S$ with
--   $$\hat\alpha_k<\hat\alpha_j\qquad\text{but}\qquad u_k>u_j,$$
--   and suppose product $k$ is in the consideration set $\Psi(S^+,p;\Delta)$. Define new markups
--   $$m'_j=m_k+\frac{\hat\alpha_j-\hat\alpha_k}{\beta},\qquad m'_k=m_j-\frac{\hat\alpha_j-\hat\alpha_k}{\beta},\qquad m'_i=m_i\ (i\neq j,k),$$
--   i.e. prices $p'_i=c_i+m'_i$. Then:
--   1. the two nominal utilities are swapped: $u'_j=u_k$ and $u'_k=u_j$;
--   2. the outside option is in the consideration set at $p'$ if and only if it is at $p$;
--   3. if every product of $S$ is considered at $p$, every product of $S$ is considered at $p'$;
--   4. the total attractiveness (the denominator of (2)) is unchanged;
--   5. the profit strictly increases: $R(S,p;\Delta)<R(S,p';\Delta)$.
--
--   In the paper this is the argument that, at optimality, the nominal utility $u_i$ is decreasing in the product index $i$ (equivalently in $\hat\alpha_i$): a pair violating the order can be swapped at a strict gain. Theorems 2 and 3 rely on it.
--
--   **Formalization Note** $\hat\alpha_j-\hat\alpha_k$ is written `(α j - β * c j) - (α k - β * c k)`, and $p'$ is built by two `Function.update`s ($j\neq k$ follows from $\hat\alpha_k<\hat\alpha_j$). The standing assumptions $\beta>0$ and $\Delta\ge0$ of §3 are hypotheses; the labelling is not needed here. The paper's product $k$ is the index $k-1$.
--
--   Differences from the source:
--   - generalization: the paper's argument is for the ordered assortment $S_n$, a pair of products $k>j$, at optimal prices at which all of $S_n$ is considered → any offer set $S$, any pair $j,k\in S$ with $\hat\alpha_k<\hat\alpha_j$ and $u_k>u_j$, any prices at which $k$ is considered; reason: the computation uses none of the extra conditions; with $S=S_n$, $k>j$ and all products considered it is the paper's step, and conclusion 3 makes the swapped prices feasible for (4), so an attained optimum of (4) has $u_i$ decreasing in $\hat\alpha_i$, the paper's claim.
--   - encoding: markups $m'_j,m'_k$ → prices $p'_j=c_j+m'_j$, $p'_k=c_k+m'_k$; products $1,\dots,N$ → `Fin N` with product $k$ at index $k-1$; reason: Lean convention, same instances.
-- source:
--   Wang, The Threshold Effects on Consumer Choice and Pricing Decisions, SSRN 3765711 (version of 2020), OS p. 1 (PDF p. 34), proof of Theorem 2, first claim

import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

namespace ThresholdMNL.Pricing

/-- Proof of Theorem 2, first claim (OS p. 1): if `α̂_j > α̂_k` but `u_k > u_j`, giving `j` the markup
`m_k + (α̂_j − α̂_k)/β` and `k` the markup `m_j − (α̂_j − α̂_k)/β` swaps the two nominal utilities,
keeps the outside option's status, keeps every product considered if all were, keeps the total
attractiveness, and strictly raises the profit (provided `k` is considered). -/
theorem exchange_step {N : ℕ} (α c : Fin N → ℝ) (β u0 Δ : ℝ) (hβ : 0 < β) (hΔ : 0 ≤ Δ)
    (S : Finset (Fin N)) (p : Fin N → ℝ) (j k : Fin N) (hj : j ∈ S) (hk : k ∈ S)
    (hα : α k - β * c k < α j - β * c j)
    (hu : nomUtil α β p j < nomUtil α β p k)
    (hkin : InCons S α β u0 Δ p k) :
    let d := ((α j - β * c j) - (α k - β * c k)) / β
    let p' := Function.update (Function.update p j (c j + (p k - c k) + d)) k
                (c k + (p j - c j) - d)
    nomUtil α β p' j = nomUtil α β p k ∧ nomUtil α β p' k = nomUtil α β p j ∧
    (OutsideInCons S α β u0 Δ p' ↔ OutsideInCons S α β u0 Δ p) ∧
    ((∀ i ∈ S, InCons S α β u0 Δ p i) → ∀ i ∈ S, InCons S α β u0 Δ p' i) ∧
    consDenom S α β u0 Δ p' = consDenom S α β u0 Δ p ∧
    profit S α c β u0 Δ p < profit S α c β u0 Δ p' := by sorry

end ThresholdMNL.Pricing
