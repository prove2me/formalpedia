-- Prove2me | Theorems.Thm_ThresholdMNL_Pricing_theorem_3
-- name    : ThresholdMNL.Pricing.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:13.053212+00:00
-- url     : https://prove2.me/theorems/1c2390df-f64c-4fd9-a1e6-c6f00829b28b
-- title:
--   Theorem 3, p. 15 — outside option considered: an optimal price has form (a) one markup on 1..n′, utility u_0 − Δ on n′+1..n, or (b) one markup on 2..n′, utility u_1 − Δ on n′+1..n
-- statement:
--   Work in the TMNL model with $\beta>0$, $\Delta\ge0$ and products labelled so that $\hat\alpha_1\ge\dots\ge\hat\alpha_N$ ($\hat\alpha_i=\alpha_i-\beta c_i$). Fix $n\in\{1,\dots,N\}$ and $S_n=\{1,\dots,n\}$, and let $\Xi(S_n,\Delta)$ be the set of prices at which every product of $S_n$ is in the consideration set. Suppose problem (4),
--   $$\max_{p\in\Xi(S_n,\Delta)}R(S_n,p;\Delta),$$
--   has an optimal price vector at which the outside option is included in the consideration set. Then (4) has an optimal price vector $p$, at which the outside option is included in the consideration set, that follows the quasi-same-markup/same-utility policy in one of two forms: for some $1\le n'\le n$,
--   1. **(a)** products $1,2,\dots,n'$ charge the same markup and products $n'+1,\dots,n$ all have nominal utility $u_0-\Delta$; or
--   2. **(b)** product $1$ charges some markup $m_1$, products $2,\dots,n'$ charge the same markup, and products $n'+1,\dots,n$ all have nominal utility $u_1-\Delta$, where $u_1$ is product $1$'s nominal utility.
--
--   Form (a) is the case where the outside option is the dominant alternative, form (b) the case where product $1$ is. Together with Theorem 2 this gives the pricing half of Theorem 4.
--
--   **Formalization Note** The standing assumptions of §3 (p. 12) are hypotheses: $\beta>0$, $\Delta\ge0$, the labelling; $1\le n\le N$. "Optimal" here is an attained maximizer over $\Xi(S_n,\Delta)$: when the outside option is considered all nominal utilities lie in $[u_0-\Delta,u_0+\Delta]$, so the feasible region is compact and the hypothesis is satisfiable. The paper's product $k$ is the index $k-1$; product $1$ is index $0$.
--
--   Differences from the source:
--   - reading: "Suppose the outside option is included in the consideration set at the optimal prices … Then, the quasi-same-markup/same-utility policy is optimal. (a) … (b) …" → if some maximizer of (4) has the outside option considered, then some maximizer with the outside option considered has form (a) or (b); reason: with ties $\hat\alpha_i=\hat\alpha_j$ two optima can differ by relabelling, so "the optimal prices have this form" can only mean that an optimum of this form exists.
--   - encoding: products $1,\dots,N$ → `Fin N` with product $k$ at index $k-1$; $\Psi$ via "for all $j$" instead of a max; reason: Lean convention, same instances.
-- source:
--   Wang, The Threshold Effects on Consumer Choice and Pricing Decisions, SSRN 3765711 (version of 2020), p. 15, Theorem 3 (proof: OS pp. 2–5 = PDF pp. 35–38)

import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

namespace ThresholdMNL.Pricing

/-- Theorem 3 (p. 15): if problem (4) on `S_n` has an optimal price vector at which the outside
option is considered, then it has one of form (a) products `1, …, n'` one markup and products
`n' + 1, …, n` nominal utility `u_0 − Δ`, or (b) product 1 free, products `2, …, n'` one markup and
products `n' + 1, …, n` nominal utility `u_1 − Δ`. -/
theorem theorem_3 {N : ℕ} (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hopt : ∃ p : Fin N → ℝ,
        (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ p i) ∧
        OutsideInCons (ordAssort N n) α β u0 Δ p ∧
        ∀ q : Fin N → ℝ, (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ q i) →
          profit (ordAssort N n) α c β u0 Δ q ≤ profit (ordAssort N n) α c β u0 Δ p) :
    let i₁ : Fin N := ⟨0, by omega⟩
    ∃ p : Fin N → ℝ,
      (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ p i) ∧
      OutsideInCons (ordAssort N n) α β u0 Δ p ∧
      (∀ q : Fin N → ℝ, (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ q i) →
          profit (ordAssort N n) α c β u0 Δ q ≤ profit (ordAssort N n) α c β u0 Δ p) ∧
      ∃ n' : ℕ, 1 ≤ n' ∧ n' ≤ n ∧
        (((∀ i j : Fin N, i.val < n' → j.val < n' → p i - c i = p j - c j) ∧
          (∀ i : Fin N, n' ≤ i.val → i.val < n → nomUtil α β p i = u0 - Δ)) ∨
         ((∀ i j : Fin N, 1 ≤ i.val → i.val < n' → 1 ≤ j.val → j.val < n' →
              p i - c i = p j - c j) ∧
          (∀ i : Fin N, n' ≤ i.val → i.val < n → nomUtil α β p i = nomUtil α β p i₁ - Δ))) := by sorry

end ThresholdMNL.Pricing
