-- Prove2me | Theorems.Thm_Supermodularity_MDP_optimal_return_supermodular_and_decision_increasing_v2
-- name    : Supermodularity.MDP.optimal_return_supermodular_and_decision_increasing_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:58.036755+00:00
-- url     : https://prove2.me/theorems/03c74cda-d0cc-46ad-9716-0d3e3ebf57fc
-- title:
--   Theorem 3.9.2 - supermodular optimal return and monotone optimal decisions (corrected: the transition law is carried by the next period's state space)
-- statement:
--   Consider a nonstationary, discounted, finite-horizon, discrete-time Markov decision process with periods $i = 1, \dots, k$. In period $i$ the state $t$ ranges over $T_i \subseteq \mathbb{R}^m$; given state $t$, the decision $x$ is restricted to a finite nonempty set $X_{t,i} \subseteq \mathbb{R}^n$. Let $S_i = \{(x,t) : t \in T_i,\ x \in X_{t,i}\}$. The expected net return of decision $x$ in state $t$ in period $i$ is $r_i(x,t)$, and $F(x,t,i,\cdot)$ is the distribution of next period's state $w \in T_{i+1}$ given $(x,t,i)$: a probability measure on $\mathbb{R}^m$ that is carried by $T_{i+1}$, i.e. $F(x,t,i,\mathbb{R}^m \setminus T_{i+1}) = 0$ for $(x,t) \in S_i$. With discount rate $\beta \in [0,1]$ and $\gamma = 1/(1+\beta)$, define from period $k$ backward
--   $$
--   g_k(x,t) = r_k(x,t), \qquad
--   f_i(t) = \max\{g_i(x,t) : x \in X_{t,i}\}, \qquad
--   g_i(x,t) = r_i(x,t) + \gamma \int f_{i+1}(w)\, dF(x,t,i,w) \ \ (i<k).
--   $$
--
--   Suppose $S_i$ is a sublattice of $\mathbb{R}^{n+m}$ for each $i$; $X_{t',i} \subseteq X_{t'',i}$ whenever $t' \le t''$ in $T_i$; $r_i(x,t)$ is increasing in $t$ on the section $\{t : (x,t) \in S_i\}$ for every $x$ and $i$, and supermodular in $(x,t)$ on $S_i$ for each $i$; and $\{F(x,t,i,\cdot)\}$ is stochastically increasing in $t$ on the section $\{t : (x,t) \in S_i\}$ for every $x$ and $i$, and stochastically supermodular in $(x,t)$ on $S_i$ for each $i$.
--
--   Then, for each period $i$:
--
--   (a) $g_i(x,t)$ is supermodular in $(x,t)$ on $S_i$;
--
--   (b) $f_i(t)$ is supermodular in $t$ on $T_i$;
--
--   (c) the set of optimal decisions $\arg\max_{x \in X_{t,i}} g_i(x,t)$ is increasing in the state $t$ on $T_i$ in the induced set order $\sqsubseteq$;
--
--   (d) there is a greatest and a least optimal decision for each state $t \in T_i$, and both are increasing in $t$ on $T_i$.
--
--   This is Topkis's Theorem 3.9.2, the capstone of Section 3.9: it combines Lemma 3.9.4 (monotonicity of $f_{i+1}$), Corollary 3.9.1(b) (stochastic supermodularity of the transition integral) and the Chapter 2 machinery (supermodularity preserved under maximization over a sublattice, Theorem 2.7.6, and increasing optimal solutions, Theorem 2.8.2).
--
--   **Formalization Note.** The retired version let the next-state law $F(x,t,i,\cdot)$ be an arbitrary probability measure on $\mathbb{R}^m$ while $f_{i+1}$ was determined by the recursion only on $T_{i+1}$; a transition law putting mass outside $T_{i+1}$ (the accepted disproof even used $T_2 = \emptyset$) then fed arbitrary values of $f_{i+1}$ into the Bellman integral and destroyed supermodularity of $f_1$. In the book $F(x,t,i,\cdot)$ is the distribution of the period-$(i+1)$ state, which lives in $T_{i+1}$; the new hypothesis `hμsupp` ($F(x,t,i,\cdot)$ gives mass $0$ to the complement of $T_{i+1}$ for every $(x,t) \in S_i$, $1 \le i < k$) makes this standing assumption of the model explicit, and it also rules out an empty $T_{i+1}$ whenever $S_i \ne \emptyset$. With it the integral depends only on $f_{i+1}|_{T_{i+1}}$, so the recursion determines $g_i$ on $S_i$ and $f_i$ on $T_i$ uniquely and quantifying over all $f, g$ satisfying it is the book's statement. As in the retired version, the maximum defining $f_i$ is `IsGreatest`, the existence of $\int f_{i+1}\,dF$ is an explicit hypothesis (the book's returns are bounded), part (c) uses the mission's `InducedSetOrder` on $\mathbb{R}^n$, and part (d) is the existence of selections $x^g, x^l$ of the greatest and least optimal decision at each state, each monotone on $T_i$. The stochastic hypotheses use the mission's `StochasticallyIncreasingOn` / `StochasticallySupermodularOn` (probability of every upward-closed set monotone, resp. supermodular, in the parameter).
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 1998 (reprint 2011), p. 165, Theorem 3.9.2 (with the model's standing assumption that F(x,t,i,·) is a distribution on the period-(i+1) state space T_{i+1} made explicit)

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn
import Definitions.Def_Supermodularity_MDP_StochasticallySupermodularOn
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

open MeasureTheory

namespace Supermodularity.MDP

/-- Theorem 3.9.2 (Topkis, *Supermodularity and Complementarity*, p. 165), corrected; the
goal of the mission. Same finite-horizon MDP model as Lemma 3.9.4
(`value_increasing_of_stochastically_increasing_v2`): periods `i = 1, …, k`, state
`t ∈ T i ⊆ ℝᵐ`, decision `x` restricted to the finite nonempty `X i t ⊆ ℝⁿ`,
`S i = {(x,t) : t ∈ T i, x ∈ X i t}`, return `r i x t`, discount `γ = 1/(1+β)`, next-state
distribution `μ i x t` **carried by the next period's state space `T (i+1)`** (`hμsupp`), and
the backward recursion (3.9.1)/(3.9.2) defining `f` and `g`. Suppose `S i` is a sublattice of
`ℝⁿ⁺ᵐ` for each `i`, `X i t' ⊆ X i t''` whenever `t' ≤ t''` in `T i`, `r i x t` is increasing in
`t` on the section of `S i` at `x` for all `x` and `i` and supermodular in `(x,t)` on `S i`
for each `i`, and `F(x,t,i,·)` is stochastically increasing in `t` on the section of `S i` at
`x` for all `x` and `i` and stochastically supermodular in `(x,t)` on `S i` for each `i`.
Then, for each period `i`: (a) `g i x t` is supermodular in `(x,t)` on `S i`; (b) `f i t` is
supermodular in `t` on `T i`; (c) the set of optimal decisions `argmax_{x ∈ X i t} g i x t` is
increasing (induced set order `⊑`) in `t` on `T i`; (d) there are a greatest and a least
optimal decision for each state `t`, each increasing in `t`.

Correction to the retired version: it let `μ i x t` be any probability measure on `ℝᵐ`, so
the Bellman integral could read values of `f (i+1)` off `T (i+1)`, where the recursion does
not determine `f (i+1)` (the accepted disproof even used `T 2 = ∅`); the book's transition
law is a distribution of the next state in `T (i+1)`, made explicit by `hμsupp`. -/
theorem optimal_return_supermodular_and_decision_increasing_v2 {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (hSlattice : ∀ i, IsSublattice (S i))
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
    (hrsuper : ∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.Monotonicity.SupermodularOn
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => r i p.1 p.2) (S i))
    (hFmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      Supermodularity.MDP.StochasticallyIncreasingOn {t | (x, t) ∈ S i} (μ i x))
    (hFsuper : ∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.MDP.StochasticallySupermodularOn (S i)
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => μ i p.1 p.2)) :
    (∀ i, 1 ≤ i → i ≤ k →
      Supermodularity.Monotonicity.SupermodularOn
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) => g i p.1 p.2) (S i)) ∧
    (∀ i, 1 ≤ i → i ≤ k → Supermodularity.Monotonicity.SupermodularOn (f i) (T i)) ∧
    (∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t t' : Fin m → ℝ⦄, t ∈ T i → t' ∈ T i → t ≤ t' →
      Supermodularity.Lattices.InducedSetOrder
        {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t}
        {x : Fin n → ℝ | x ∈ X i t' ∧ ∀ y ∈ X i t', g i y t' ≤ g i x t'}) ∧
    (∃ xg xl : ℕ → (Fin m → ℝ) → (Fin n → ℝ),
      (∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
        IsGreatest {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} (xg i t)) ∧
      (∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
        IsLeast {x : Fin n → ℝ | x ∈ X i t ∧ ∀ y ∈ X i t, g i y t ≤ g i x t} (xl i t)) ∧
      (∀ i, 1 ≤ i → i ≤ k → MonotoneOn (xg i) (T i)) ∧
      (∀ i, 1 ≤ i → i ≤ k → MonotoneOn (xl i) (T i))) := by sorry

end Supermodularity.MDP
