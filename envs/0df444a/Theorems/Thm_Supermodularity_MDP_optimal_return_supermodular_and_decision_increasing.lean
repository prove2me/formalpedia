-- Prove2me | Theorems.Thm_Supermodularity_MDP_optimal_return_supermodular_and_decision_increasing
-- name    : Supermodularity.MDP.optimal_return_supermodular_and_decision_increasing
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:33.989466+00:00
-- url     : https://prove2.me/theorems/b920d256-8282-4e53-bdb0-b38f8d5b5861
-- title:
--   Theorem 3.9.2 - supermodular optimal return and monotone optimal decisions
-- statement:
--   Same finite-horizon Markov decision process as Lemma 3.9.4: periods $i = 1,\dots,k$, state
--   $t \in T_i \subseteq \mathbb{R}^m$, decision $x$ restricted to the finite nonempty
--   $X_{t,i} \subseteq \mathbb{R}^n$, $S_i = \{(x,t) : t \in T_i,\, x \in X_{t,i}\}$, return
--   $r_i(x,t)$, discount $\gamma = 1/(1+\beta)$, transition law $F(x,t,i,\cdot)$, and the backward
--   recursion $g_k(x,t) = r_k(x,t)$, $f_i(t) = \max_{x \in X_{t,i}} g_i(x,t)$, $g_i(x,t) =
--   r_i(x,t) + \gamma \int f_{i+1}(w)\, dF(x,t,i,w)$ for $i<k$.
--
--   Suppose $S_i$ is a sublattice of $\mathbb{R}^{n+m}$ for each $i$; $X_{t',i} \subseteq
--   X_{t'',i}$ whenever $t' \le t''$ in $T_i$; $r_i(x,t)$ is increasing in $t$ on the section of
--   $S_i$ at $x$, for every $x$ and $i$, and supermodular in $(x,t)$ on $S_i$, for each $i$; and
--   $\{F(x,t,i,\cdot)\}$ is stochastically increasing in $t$ on the section of $S_i$ at $x$, for
--   every $x$ and $i$, and stochastically supermodular in $(x,t)$ on $S_i$, for each $i$.
--
--   Then, for each period $i$:
--
--   (a) $g_i(x,t)$ is supermodular in $(x,t)$ on $S_i$;
--
--   (b) $f_i(t)$ is supermodular in $t$ on $T_i$;
--
--   (c) the set of optimal decisions $\arg\max_{x \in X_{t,i}} g_i(x,t)$ is increasing (in the
--   induced set order $\sqsubseteq$) in the state $t$ on $T_i$;
--
--   (d) there is a greatest and a least optimal decision for each state $t$, and both are
--   increasing in $t$.
--
--   This is Topkis's Theorem 3.9.2, the capstone of Section 3.9: it identifies conditions under
--   which optimal policies of a Markov decision process are monotone in the state, by combining
--   Lemma 3.9.4 (monotonicity), Corollary 3.9.1(b) (stochastic supermodularity of the transition
--   integral), and the chapter 2 machinery for supermodularity preserved under maximization
--   (Theorem 2.7.6) and increasing optimal solutions (Theorem 2.8.2).
--
--   **Formalization Note.** As in Lemma 3.9.4, $f$ and $g$ are quantified as functions satisfying
--   the two defining recursion equations rather than constructed by the mission. Part (c) uses the
--   mission series' `InducedSetOrder` (the strong/Veinott set order) from chunk `01-lattices`.
--   Part (d) is stated as the existence of selection functions $x^g, x^l : T_i \to X_{t,i}$
--   (greatest, least optimal decision at each state) that are each monotone in $t$.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 165, Theorem 3.9.2

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn
import Definitions.Def_Supermodularity_MDP_StochasticallySupermodularOn
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

open MeasureTheory

namespace Supermodularity.MDP

/-- Theorem 3.9.2 (p. 165, PDF 178), the goal of this mission. Same finite-horizon MDP
model as Lemma 3.9.4 (`value_increasing_of_stochastically_increasing`): periods
`i = 1, …, k`, state `t ∈ T i ⊆ Rᵐ`, decision `x` restricted to the finite nonempty
`X i t ⊆ Rⁿ`, `S i = {(x,t) : t ∈ T i, x ∈ X i t}`, return `r i x t`, discount
`γ = 1/(1+β)`, next-state distribution `μ i x t`, and the backward recursion (3.9.1)/
(3.9.2) defining `f` and `g`. Suppose `S i` is a sublattice of `Rⁿ⁺ᵐ` for each `i`,
`X t' i ⊆ X t'' i` whenever `t' ≤ t''` in `T i`, `r i x t` is increasing in `t` on the
section of `S i` at `x` for all `x` and `i` and is supermodular in `(x,t)` on `S i` for
each `i`, and `F(x,t,i,·)` is stochastically increasing in `t` on the section of `S i`
at `x` for all `x` and `i` and is stochastically supermodular in `(x,t)` on `S i` for
each `i`. Then, for each period `i`: (a) `g i x t` is supermodular in `(x,t)` on `S i`;
(b) `f i t` is supermodular in `t` on `T i`; (c) the set of optimal decisions
`argmax_{x ∈ X i t} g i x t` is increasing (in the induced set order `⊑`) in the state
`t` on `T i`; and (d) there is a greatest (least) optimal decision for each state `t`,
increasing in `t`. -/
theorem optimal_return_supermodular_and_decision_increasing {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (hSlattice : ∀ i, IsSublattice (S i))
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
