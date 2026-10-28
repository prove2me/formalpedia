-- Prove2me | Theorems.Thm_ThresholdMNL_Pricing_theorem_2
-- name    : ThresholdMNL.Pricing.theorem_2
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:12.372983+00:00
-- url     : https://prove2.me/theorems/eaac6423-adb1-4b48-abfd-444e288e5638
-- title:
--   Theorem 2, p. 14 — outside option priced out: markup m*_1 for product 1, one markup m on 2..n′, nominal utility u_0 on n′+1..n (value at the closure point m*_1); unimodal in m
-- statement:
--   Work in the TMNL model with $\beta>0$, $\Delta\ge0$ and products labelled so that $\hat\alpha_1\ge\dots\ge\hat\alpha_N$ ($\hat\alpha_i=\alpha_i-\beta c_i$). Fix $n\in\{1,\dots,N\}$ and the ordered assortment $S_n=\{1,\dots,n\}$. Let $\Xi(S_n,\Delta)$ be the set of prices at which every product of $S_n$ is in the consideration set, and let $V$ be the optimal value of problem (4),
--   $$V=\sup_{p\in\Xi(S_n,\Delta)}R(S_n,p;\Delta).$$
--   Suppose that the outside option is not included in the consideration set at the optimal prices, in the sense that $V$ is also the supremum of $R(S_n,p;\Delta)$ over the prices $p\in\Xi(S_n,\Delta)$ at which the outside option is not considered. Set
--   $$m^*_1=\frac{\hat\alpha_1-u_0-\Delta}{\beta}.$$
--   For $1\le n'\le n$ and a real $m$, let $\bar p(n',m)$ be the prices giving product $1$ the markup $m^*_1$ (so $u_1=u_0+\Delta$), products $2,\dots,n'$ the common markup $m$, and products $n'+1,\dots,n$ the nominal utility $u_0$. Write $\bar R(n',m)=\sum_{i\in S_n}m_ie^{u_i}/\sum_{i\in S_n}e^{u_i}$ for the profit at $\bar p(n',m)$ with the outside option excluded. Then:
--   1. **(a)** if $n=1$ (only product $1$ is offered), $V=m^*_1$;
--   2. **(b)** there are $1\le n'\le n$ and $m$ such that $V=\bar R(n',m)$ and every product of $S_n$ has nominal utility in $[u_0,u_0+\Delta]$ at $\bar p(n',m)$; moreover, if $n'\ge2$, the profit $m\mapsto\bar R(n',m)$ is strictly unimodal: strictly increasing on $(-\infty,m_0]$ and strictly decreasing on $[m_0,\infty)$ for some $m_0$.
--
--   Since $u_1=u_0+\Delta$ exactly at $\bar p$, the outside option sits on the boundary of the consideration set there; the paper's prices $m^*_1-\epsilon$ (and tail nominal utilities $u_0+\beta\epsilon$) approach $\bar p$, and their profits approach $\bar R(n',m)=V$. This is the outside-excluded case of the quasi-same-markup/same-utility policy of Theorem 4.
--
--   **Formalization Note** The standing assumptions of §3 (p. 12) are hypotheses: $\beta>0$, $\Delta\ge0$, the labelling; $1\le n\le N$ because $S_n$ with $n\in\mathcal N$ is named. Optimal values are least upper bounds (`IsLUB`) with the explicit value $V$. In Lean $\bar p$ is `pbar n' m`: index $0$ gets price $c+m^*_1$, indices $1,\dots,n'-1$ get $c+m$, the other indices get $(\alpha_i-u_0)/\beta$; $\bar R$ is `exclProfit (ordAssort N n)`. The paper's product $k$ is the index $k-1$.
--
--   Differences from the source:
--   - reading: "the outside option is not included in the consideration set at the optimal prices for the offer set $S_n$" → $V$, the supremum of (4) over $\Xi(S_n,\Delta)$, equals the supremum over the part of $\Xi(S_n,\Delta)$ where the outside option is not considered; reason: on that part the optimum is never attained (it requires $u_1>u_0+\Delta$ strictly), so "at the optimal prices" can only refer to the supremum.
--   - reading: "markup $m^*_1:=(\hat\alpha_1-u_0-\Delta)/\beta-\epsilon$, $\epsilon$ an arbitrarily small positive number", and in (b) tail nominal utility "equal to $u_0$" → the closure point $\epsilon=0$, markup $(\hat\alpha_1-u_0-\Delta)/\beta$ and tail utility exactly $u_0$, with value given by the continuous outside-excluded profit formula of OS p. 2 and the closure condition $u_i\in[u_0,u_0+\Delta]$; reason: no price with $\epsilon>0$ fixed is optimal; the supremum is the limit as $\epsilon\to0^+$, which is the value at the closure point.
--   - reading: "the profit function is strictly unimodal in $m$" → for $n'\ge2$, strictly increasing on $(-\infty,m_0]$ and strictly decreasing on $[m_0,\infty)$; reason: the standard meaning; for $n'=1$ there is no common-markup group and no $m$.
--   - reading: "(a) It is optimal to offer only product 1 at markup $m^*_1$" → if $n=1$ then $V=m^*_1$; reason: (a) is the case $S_n=S_1$ of the theorem, whose value is $m^*_1$ read through the closure point as above.
--   - encoding: products $1,\dots,N$ → `Fin N` with product $k$ at index $k-1$; $\Psi$ via "for all $j$" instead of a max; reason: Lean convention, same instances.
-- source:
--   Wang, The Threshold Effects on Consumer Choice and Pricing Decisions, SSRN 3765711 (version of 2020), p. 14, Theorem 2 (proof: OS pp. 1–2 = PDF pp. 34–35)

import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

namespace ThresholdMNL.Pricing

/-- Theorem 2 (p. 14): if the optimal value `V` of problem (4) on `S_n` is the value over the
feasible prices at which the outside option is not considered, then it is the value of the
outside-excluded profit at the closure point where product 1 has markup
`m*_1 = (α̂_1 − u_0 − Δ)/β`, products `2, …, n'` a common markup `m`, and products `n' + 1, …, n`
nominal utility `u_0`; (a) for `n = 1` the value is `m*_1`; the profit is strictly unimodal in `m`. -/
theorem theorem_2 {N : ℕ} (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (V : ℝ)
    (hV : IsLUB {x | ∃ p : Fin N → ℝ,
        (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ p i) ∧
        x = profit (ordAssort N n) α c β u0 Δ p} V)
    (hexcl : IsLUB {x | ∃ p : Fin N → ℝ,
        (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ p i) ∧
        ¬ OutsideInCons (ordAssort N n) α β u0 Δ p ∧
        x = profit (ordAssort N n) α c β u0 Δ p} V) :
    let i₁ : Fin N := ⟨0, by omega⟩
    let m₁ : ℝ := (α i₁ - β * c i₁ - u0 - Δ) / β
    let pbar : ℕ → ℝ → Fin N → ℝ := fun n' m i =>
      if i.val = 0 then c i + m₁ else if i.val < n' then c i + m else (α i - u0) / β
    (n = 1 → V = m₁) ∧
    ∃ (n' : ℕ) (m : ℝ), 1 ≤ n' ∧ n' ≤ n ∧
      V = exclProfit (ordAssort N n) α c β (pbar n' m) ∧
      (∀ i ∈ ordAssort N n,
        u0 ≤ nomUtil α β (pbar n' m) i ∧ nomUtil α β (pbar n' m) i ≤ u0 + Δ) ∧
      (2 ≤ n' → ∃ m₀ : ℝ,
        StrictMonoOn (fun m' => exclProfit (ordAssort N n) α c β (pbar n' m')) (Set.Iic m₀) ∧
        StrictAntiOn (fun m' => exclProfit (ordAssort N n) α c β (pbar n' m')) (Set.Ici m₀)) := by sorry

end ThresholdMNL.Pricing
