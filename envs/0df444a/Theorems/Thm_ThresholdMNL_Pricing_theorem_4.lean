-- Prove2me | Theorems.Thm_ThresholdMNL_Pricing_theorem_4
-- name    : ThresholdMNL.Pricing.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:19.623984+00:00
-- url     : https://prove2.me/theorems/20b08ece-a606-48de-b5bb-ae50a5499eee
-- title:
--   Theorem 4, p. 16 — a utility-net-cost ordered assortment with quasi-same-markup/same-utility prices reaches the optimal profit of (3) (as a supremum; attained when (3) has a maximizer)
-- statement:
--   Consider the TMNL joint assortment and pricing problem (3): products $1,\dots,N$ ($N\ge1$) with intrinsic utilities $\alpha_i$, unit costs $c_i$, price coefficient $\beta>0$, outside-option nominal utility $u_0$ and tolerance $\Delta\ge0$, labelled so that $\hat\alpha_1\ge\dots\ge\hat\alpha_N$ with $\hat\alpha_i=\alpha_i-\beta c_i$. A consumer considers the alternatives $\Psi(S^+,p;\Delta)$ whose nominal utility is within $\Delta$ of the best one in $S^+=S\cup\{0\}$ and chooses among them by the multinomial logit; the firm earns $R(S,p;\Delta)=\sum_{i\in\Psi}(p_i-c_i)q_i(S,p;\Delta)$. Let
--   $$V=\sup_{S\subseteq\mathcal N,\ p}R(S,p;\Delta).$$
--   Then there is $n\in\{1,\dots,N\}$ such that
--
--   1. the utility-net-cost ordered assortment $S_n=\{1,\dots,n\}$ is an optimal offer set: $\sup_pR(S_n,p;\Delta)=V$; and
--   2. the quasi-same-markup/same-utility policy is an optimal pricing strategy on it:
--   $$\sup\big\{R(S_n,p;\Delta):\ p\text{ quasi-same-markup/same-utility on }S_n\text{ for some }n'\big\}=V,$$
--   where $p$ is quasi-same-markup/same-utility (Definition 2) if, for some $1\le n'\le n$, products $2,\dots,n'$ have equal markups $p_i-c_i$ and products $n'+1,\dots,n$ have equal nominal utilities $\alpha_i-\beta p_i$;
--   3. whenever (3) has a maximizer (some $S$ and $p$ with $R(S,p;\Delta)=V$), some quasi-same-markup/same-utility price vector $p$ on $S_n$ attains $R(S_n,p;\Delta)=V$.
--
--   This is the paper's summary of its joint assortment and pricing results: the search over all $2^N$ offer sets and all price vectors reduces to $N$ nested assortments and to prices that, beyond product $1$, form one equal-markup group and one equal-utility group.
--
--   **Formalization Note** "Optimal" is read as "attains the optimal value": the theorem asserts a real $V$ that is the least upper bound of $R$ over all offer sets and prices, and also over the prices on $S_n$, and also over the quasi-same-markup/same-utility prices on $S_n$; and when $V$ is attained by some offer set and prices, it is attained by quasi-same-markup/same-utility prices on $S_n$. The standing assumptions of §3 (p. 12) are hypotheses: $\beta>0$, the labelling, and $\Delta\ge0$; $N\ge1$ because $S_n$ with $n\in\mathcal N$ must exist. The paper's product $k$ is the index $k-1$: Definition 2's products $2,\dots,n'$ are the indices $1,\dots,n'-1$ and its products $n'+1,\dots,n$ the indices $n',\dots,n-1$. For $N\le3$ every price vector satisfies Definition 2 (take $n'=2$), as in the paper, so the pricing clause has content from $N=4$ on.
--
--   Differences from the source:
--   - reading: "optimal offer set" and "optimal pricing strategy" for the "max" problem (3) → the supremum of $R$ over prices on $S_n$, and over quasi-same-markup/same-utility prices on $S_n$, equals the supremum $V$ of (3), and whenever $V$ is attained some quasi-same-markup/same-utility price vector on $S_n$ attains it; reason: (3) need not have a maximizer — with $N=1$, $\beta=1$, $\alpha_1=10$, $c_1=0$, $u_0=0$, $\Delta=0.1$ the profit is $m$ for markups $m<9.9$ and at most $5.31$ otherwise, so $\sup R=9.9$ is not attained (the paper's own $m^*_1-\epsilon$ in Theorem 2(a)).
--   - encoding: products $1,\dots,N$ and $S_n$ → `Fin N` with product $k$ at index $k-1$ and $S_n$ the indices below $n$; reason: Lean convention, same instances.
--   - encoding: $\Psi$ defined with $\max_{j\in S^+}u_j$ → "$u_i\ge u_j-\Delta$ for all $j\in S^+$", outside option as the parameter $u_0$, prices on all of $\mathcal N$; reason: equivalent for the finite nonempty $S^+$; prices off $S$ enter no term.
-- source:
--   Wang, The Threshold Effects on Consumer Choice and Pricing Decisions, SSRN 3765711 (version of 2020), p. 16, Theorem 4 (with Definitions 1–2, pp. 13–14)

import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

namespace ThresholdMNL.Pricing

/-- Theorem 4 (p. 16): a utility-net-cost ordered assortment `S_n` is an optimal offer set and the
quasi-same-markup/same-utility policy on it is an optimal pricing strategy for problem (3), both
read as attaining the optimal value `V`, the least upper bound of `R(S, p; Δ)` over all offer sets
and prices; when (3) has a maximizer, a quasi-same-markup/same-utility price vector on `S_n`
is one. -/
theorem theorem_4 {N : ℕ} (hN : 1 ≤ N) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i) :
    ∃ V : ℝ,
      IsLUB {x | ∃ (S : Finset (Fin N)) (p : Fin N → ℝ), x = profit S α c β u0 Δ p} V ∧
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
        IsLUB {x | ∃ p : Fin N → ℝ, x = profit (ordAssort N n) α c β u0 Δ p} V ∧
        IsLUB {x | ∃ (n' : ℕ) (p : Fin N → ℝ),
            IsQuasiSameMarkupSameUtility α c β n n' p ∧
            x = profit (ordAssort N n) α c β u0 Δ p} V ∧
        ((∃ (S : Finset (Fin N)) (p : Fin N → ℝ), profit S α c β u0 Δ p = V) →
          ∃ (n' : ℕ) (p : Fin N → ℝ), IsQuasiSameMarkupSameUtility α c β n n' p ∧
            profit (ordAssort N n) α c β u0 Δ p = V) := by sorry

end ThresholdMNL.Pricing
