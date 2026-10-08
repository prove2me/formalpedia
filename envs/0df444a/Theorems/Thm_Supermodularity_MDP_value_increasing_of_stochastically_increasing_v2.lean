-- Prove2me | Theorems.Thm_Supermodularity_MDP_value_increasing_of_stochastically_increasing_v2
-- name    : Supermodularity.MDP.value_increasing_of_stochastically_increasing_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:49.371733+00:00
-- url     : https://prove2.me/theorems/816263b1-88fe-43dd-a93f-bc2514296d63
-- title:
--   Lemma 3.9.4 - the optimal-value function is increasing in the state (corrected: the transition law is carried by the next period's state space)
-- statement:
--   Consider a nonstationary, discounted, finite-horizon, discrete-time Markov decision process with periods $i = 1, \dots, k$. In period $i$ the state $t$ ranges over $T_i \subseteq \mathbb{R}^m$; given state $t$, the decision $x$ is restricted to a finite nonempty set $X_{t,i} \subseteq \mathbb{R}^n$. Let $S_i = \{(x,t) : t \in T_i,\ x \in X_{t,i}\}$. The expected net return of decision $x$ in state $t$ in period $i$ is $r_i(x,t)$, and $F(x,t,i,\cdot)$ is the distribution of next period's state $w \in T_{i+1}$ given $(x,t,i)$: a probability measure on $\mathbb{R}^m$ that is carried by $T_{i+1}$, i.e. $F(x,t,i,\mathbb{R}^m \setminus T_{i+1}) = 0$ for $(x,t) \in S_i$. With discount rate $\beta \in [0,1]$ and $\gamma = 1/(1+\beta)$, define from period $k$ backward
--   $$
--   g_k(x,t) = r_k(x,t), \qquad
--   f_i(t) = \max\{g_i(x,t) : x \in X_{t,i}\}, \qquad
--   g_i(x,t) = r_i(x,t) + \gamma \int f_{i+1}(w)\, dF(x,t,i,w) \ \ (i<k).
--   $$
--
--   Suppose $X_{t',i} \subseteq X_{t'',i}$ whenever $t' \le t''$ in $T_i$, $r_i(x,t)$ is increasing in $t$ on the section $\{t : (x,t) \in S_i\}$ for every $x$ and $i$, and $\{F(x,t,i,\cdot)\}$ is stochastically increasing in $t$ on that same section for every $x$ and $i$.
--
--   Then $f_i(t)$ is increasing in $t$ on $T_i$ for every period $i$.
--
--   This is Topkis's Lemma 3.9.4, proved by backward induction on the period: if $f_{i+1}$ is increasing on $T_{i+1}$, then $g_i(x,\cdot)$ is increasing by stochastic monotonicity of the transition law, hence $f_i$ is increasing by the growing constraint sets. It is the base that Theorem 3.9.2 builds on.
--
--   **Formalization Note.** The retired version let the next-state law $F(x,t,i,\cdot)$ be an arbitrary probability measure on $\mathbb{R}^m$ while $f_{i+1}$ was determined by the recursion only on $T_{i+1}$; a transition law putting mass outside $T_{i+1}$ then fed arbitrary (decreasing) values of $f_{i+1}$ into the Bellman integral, and the lemma was disproved. In the book $F(x,t,i,\cdot)$ is the distribution of the period-$(i+1)$ state, which lives in $T_{i+1}$; the new hypothesis `hμsupp` ($F(x,t,i,\cdot)$ gives mass $0$ to the complement of $T_{i+1}$ for every $(x,t) \in S_i$, $1 \le i < k$) makes this standing assumption of the model explicit. With it the integral depends only on $f_{i+1}|_{T_{i+1}}$, so the recursion determines $g_i$ on $S_i$ and $f_i$ on $T_i$ uniquely and the statement, which quantifies over all $f, g$ satisfying the recursion, is the book's lemma. As in the retired version, the maximum defining $f_i$ is expressed as `IsGreatest` (attained since $X_{t,i}$ is finite and nonempty), the existence of the integrals $\int f_{i+1}\,dF$ is an explicit hypothesis (the book's returns are bounded), and the stochastic-monotonicity hypothesis uses the mission's `StochasticallyIncreasingOn` (monotone probability of every upward-closed set).
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 1998 (reprint 2011), p. 161-162, Lemma 3.9.4 (with the model's standing assumption that F(x,t,i,·) is a distribution on the period-(i+1) state space T_{i+1} made explicit)

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn

open MeasureTheory

namespace Supermodularity.MDP

/-- Lemma 3.9.4 (Topkis, *Supermodularity and Complementarity*, p. 161–162), corrected.
A finite-horizon, nonstationary, discounted, discrete-time Markov decision process with
periods `i = 1, …, k`: state `t ∈ T i ⊆ ℝᵐ`, decision `x` restricted to the finite nonempty
set `X i t ⊆ ℝⁿ`, `S i = {(x,t) : t ∈ T i, x ∈ X i t}`, return `r i x t`, discount
`γ = 1/(1+β)`, and next-state distribution `μ i x t`, **a distribution of the period-`i+1`
state, i.e. carried by `T (i+1)`** (`hμsupp`). Starting from `g k x t = r k x t`, `f` and `g`
satisfy the backward recursion `f i t = max {g i x t : x ∈ X i t}` (3.9.1) and, for `i < k`,
`g i x t = r i x t + γ ∫ f (i+1) w dμ (i x t) w` (3.9.2). If `X i t' ⊆ X i t''` whenever
`t' ≤ t''` in `T i`, `r i x t` is increasing in `t` on the section of `S i` at `x` for all `x`
and `i`, and `F(x,t,i,·)` is stochastically increasing in `t` on that section for all `x` and
`i`, then `f i t` is increasing in `t` on `T i` for each `i`.

Correction to the retired version: it let `μ i x t` be any probability measure on `ℝᵐ`, so the
Bellman integral could read values of `f (i+1)` off `T (i+1)`, where the recursion does not
determine `f (i+1)`; the book's transition law is a distribution of the next state in
`T (i+1)`, which `hμsupp` makes explicit. With it, the recursion pins `g` on `S i` and `f` on
`T i` uniquely, so quantifying over all `f`, `g` satisfying it is the book's statement. -/
theorem value_increasing_of_stochastically_increasing_v2 {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (r : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (μ : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → Measure (Fin m → ℝ))
    (hμprob : ∀ i x t, IsProbabilityMeasure (μ i x t))
    (hμsupp : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → μ i x t (T (i + 1))ᶜ = 0)
    (f : ℕ → (Fin m → ℝ) → ℝ) (g : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hgk : ∀ x t, g k x t = r k x t)
    (hg : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i →
      g i x t = r i x t + (1 / (1 + β)) * ∫ w, f (i + 1) w ∂ (μ i x t))
    (hfint : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → Integrable (f (i + 1)) (μ i x t))
    (hf : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
      IsGreatest ((fun x => g i x t) '' (X i t : Set (Fin n → ℝ))) (f i t))
    (hXne : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i, (X i t).Nonempty)
    (hXsub : ∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t' t'' : Fin m → ℝ⦄, t' ∈ T i → t'' ∈ T i → t' ≤ t'' →
      X i t' ⊆ X i t'')
    (hrmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x, MonotoneOn (fun t => r i x t) {t | (x, t) ∈ S i})
    (hFmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      Supermodularity.MDP.StochasticallyIncreasingOn {t | (x, t) ∈ S i} (μ i x)) :
    ∀ i, 1 ≤ i → i ≤ k → MonotoneOn (f i) (T i) := by sorry

end Supermodularity.MDP
