-- Prove2me | Theorems.Thm_Supermodularity_MDP_value_increasing_of_stochastically_increasing
-- name    : Supermodularity.MDP.value_increasing_of_stochastically_increasing
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:30:47.195981+00:00
-- url     : https://prove2.me/theorems/e4c4e4da-a57d-4c3d-907d-a092eedf3582
-- title:
--   Lemma 3.9.4 - the optimal-value function is increasing in the state
-- statement:
--   Consider a nonstationary, discounted, finite-horizon, discrete-time Markov decision process
--   with periods $i = 1, \dots, k$. In period $i$ the state $t$ ranges over $T_i \subseteq
--   \mathbb{R}^m$; given state $t$, the decision $x$ is restricted to a finite nonempty set
--   $X_{t,i} \subseteq \mathbb{R}^n$. Let $S_i = \{(x,t) : t \in T_i,\, x \in X_{t,i}\}$. The
--   (bounded) expected net return of decision $x$ in state $t$, period $i$, is $r_i(x,t)$, and
--   $F(x,t,i,w)$ is the distribution of next period's state $w$ given $(x,t,i)$. With discount
--   rate $\beta \in [0,1]$ and $\gamma = 1/(1+\beta)$, define, from period $k$ backward,
--   $$
--   g_k(x,t) = r_k(x,t), \qquad
--   f_i(t) = \max\{g_i(x,t) : x \in X_{t,i}\}, \qquad
--   g_i(x,t) = r_i(x,t) + \gamma \int f_{i+1}(w)\, dF(x,t,i,w) \ \ (i<k).
--   $$
--
--   Suppose $X_{t',i} \subseteq X_{t'',i}$ whenever $t' \le t''$ in $T_i$, $r_i(x,t)$ is increasing
--   in $t$ on the section $\{t : (x,t) \in S_i\}$ for every $x$ and $i$, and $\{F(x,t,i,\cdot)\}$
--   is stochastically increasing in $t$ on that same section for every $x$ and $i$.
--
--   Then $f_i(t)$ is increasing in $t$ on $T_i$ for every period $i$.
--
--   This is Topkis's Lemma 3.9.4, proved by backward induction on the period: if $g_{i+1}(x,\cdot)$
--   is increasing, so is $f_{i+1}$ (by the growing constraint sets), hence so is $g_i(x,\cdot)$ (by
--   stochastic monotonicity of the transition law), hence so is $f_i$. It is the base case that
--   Theorem 3.9.2 builds on to obtain supermodularity as well as monotonicity.
--
--   **Formalization Note.** $f$ and $g$ are quantified as *any* functions satisfying the two
--   defining equations above (the equations determine them uniquely by backward induction from
--   period $k$); the mission does not itself construct the recursion. The maximum in the
--   definition of $f_i(t)$ is expressed as `IsGreatest`, since $X_{t,i}$ is a nonempty finite set.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 161-162, Lemma 3.9.4

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn

open MeasureTheory

namespace Supermodularity.MDP

/-- Lemma 3.9.4 (p. 161–162, PDF 174–175). A finite-horizon, nonstationary, discounted,
discrete-time Markov decision process with periods `i = 1, …, k`: state `t ∈ T i ⊆ Rᵐ`,
decision `x` restricted to the finite nonempty set `X i t ⊆ Rⁿ`, `S i = {(x,t) : t ∈ T i,
x ∈ X i t}`, return `r i x t`, discount `γ = 1/(1+β)`, next-state distribution `μ i x t`
on `Rᵐ`. Starting from `g k x t = r k x t`, `f` and `g` satisfy the backward recursion
`f i t = max {g i x t : x ∈ X i t}` (3.9.1) and, for `i < k`, `g i x t = r i x t +
γ ∫ f (i+1) w dμ (i x t) w` (3.9.2). If `X t' i ⊆ X t'' i` whenever `t' ≤ t''` in `T i`,
`r i x t` is increasing in `t` on the section of `S i` at `x` for all `x` and `i`, and
`F(x,t,i,·)` is stochastically increasing in `t` on the section of `S i` at `x` for all
`x` and `i`, then `f i t` is increasing in `t` on `T i` for each `i`. -/
theorem value_increasing_of_stochastically_increasing {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (r : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (μ : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → Measure (Fin m → ℝ))
    (hμprob : ∀ i x t, IsProbabilityMeasure (μ i x t))
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
