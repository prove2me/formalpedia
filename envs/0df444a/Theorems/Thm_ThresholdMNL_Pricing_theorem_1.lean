-- Prove2me | Theorems.Thm_ThresholdMNL_Pricing_theorem_1
-- name    : ThresholdMNL.Pricing.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:09.212988+00:00
-- url     : https://prove2.me/theorems/1b037a9a-d8e8-44ec-8a93-c65ac85c21e3
-- title:
--   Theorem 1, p. 13 — some utility-net-cost ordered assortment S_{n*} is an optimal offer set for (3) (as a supremum)
-- statement:
--   Consider the TMNL joint assortment and pricing problem (3): products $1,\dots,N$ ($N\ge1$) with intrinsic utilities $\alpha_i$, costs $c_i$, price coefficient $\beta>0$, outside-option utility $u_0$ and tolerance $\Delta\ge0$, labelled so that $\hat\alpha_1\ge\hat\alpha_2\ge\dots\ge\hat\alpha_N$, where $\hat\alpha_i=\alpha_i-\beta c_i$. Let
--   $$V=\sup_{S\subseteq\mathcal N,\ p}R(S,p;\Delta)$$
--   be the optimal value of (3). Then there is $n^*\in\{1,\dots,N\}$ such that the utility-net-cost ordered assortment $S_{n^*}=\{1,\dots,n^*\}$ reaches it:
--   $$\sup_{p}R(S_{n^*},p;\Delta)=V,$$
--   and, whenever (3) has a maximizer (some $S$ and $p$ with $R(S,p;\Delta)=V$), some price vector $p$ attains $R(S_{n^*},p;\Delta)=V$.
--
--   This is the assortment half of the paper's main result (Theorem 4): only the $N$ nested sets $S_1\subset\dots\subset S_N$ need to be searched.
--
--   **Formalization Note** The theorem asserts the existence of a real $V$ that is the least upper bound of $R(S,p;\Delta)$ over all offer sets and price vectors, and of an $n^*$ for which $V$ is also the least upper bound over the prices on $S_{n^*}$ and, if $V$ is attained by some offer set, is attained on $S_{n^*}$. The standing assumptions of §3 (p. 12) are hypotheses: $\beta>0$, the labelling $\hat\alpha$ non-increasing, and $\Delta\ge0$ (the tolerance of the model); $N\ge1$ because $S_{n^*}$ with $n^*\in\mathcal N$ must exist. The paper's product $k$ is the index $k-1$.
--
--   Differences from the source:
--   - reading: "optimal offer set" for the "max" problem (3) → the supremum of $R$ over prices on $S_{n^*}$ equals the supremum $V$ of (3), and $S_{n^*}$ attains $V$ whenever some offer set does; reason: (3) need not have a maximizer — with $N=1$, $\beta=1$, $\alpha_1=10$, $c_1=0$, $u_0=0$, $\Delta=0.1$ the profit is $m$ for markups $m<9.9$ and at most $5.31$ otherwise, so $\sup R=9.9$ is not attained (the paper's own $m^*_1-\epsilon$ in Theorem 2(a)).
--   - encoding: products $1,\dots,N$ and $S_n=\{1,\dots,n\}$ → `Fin N` with product $k$ at index $k-1$ and $S_n$ the indices below $n$; reason: Lean convention, same instances.
--   - encoding: $\Psi$ defined with $\max_{j\in S^+}u_j$ → "$u_i\ge u_j-\Delta$ for all $j\in S^+$", outside option as the parameter $u_0$, prices on all of $\mathcal N$; reason: equivalent for the finite nonempty $S^+$; prices off $S$ enter no term.
-- source:
--   Wang, The Threshold Effects on Consumer Choice and Pricing Decisions, SSRN 3765711 (version of 2020), p. 13, Theorem 1 (proof: Appendix B, p. 29)

import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

namespace ThresholdMNL.Pricing

/-- Theorem 1 (p. 13): some utility-net-cost ordered assortment `S_{n*}` is an optimal offer set
for problem (3), "optimal" read as attaining the optimal value `V`, the least upper bound of
`R(S, p; Δ)` over all offer sets and prices; when (3) has a maximizer, `S_{n*}` carries one. -/
theorem theorem_1 {N : ℕ} (hN : 1 ≤ N) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i) :
    ∃ V : ℝ,
      IsLUB {x | ∃ (S : Finset (Fin N)) (p : Fin N → ℝ), x = profit S α c β u0 Δ p} V ∧
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
        IsLUB {x | ∃ p : Fin N → ℝ, x = profit (ordAssort N n) α c β u0 Δ p} V ∧
        ((∃ (S : Finset (Fin N)) (p : Fin N → ℝ), profit S α c β u0 Δ p = V) →
          ∃ p : Fin N → ℝ, profit (ordAssort N n) α c β u0 Δ p = V) := by sorry

end ThresholdMNL.Pricing
