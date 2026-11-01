-- Prove2me | Theorems.Thm_SambaPG_theorem_1
-- name    : SambaPG.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:41.525719+00:00
-- url     : https://prove2.me/theorems/73851197-5850-42e4-9e3c-2985e59b3ee5
-- title:
--   Theorem 1 — SAMBA is a Markov chain, $p_{a^\star}(t)\to1$ a.s., and $\mathcal Rg(T)\le\frac{N}{\alpha\Delta}\log T+Q$
-- statement:
--   Consider a Bernoulli bandit with $N\ge2$ arms, means $r_a\in[0,1]$ and a unique optimal arm $a^\star$, optimal mean $r^\star$ and gap $\Delta$. Run SAMBA with learning rate $\alpha\in(0,1)$ from the uniform vector $p_a(0)=1/N$. If
--
--   $$
--   \alpha<\frac{\Delta}{r^\star-\Delta},\qquad(2)
--   $$
--
--   then:
--
--   1. the SAMBA process $(p(t):t\in\mathbb Z_+)$ is a Markov chain: given the history up to time $t$, $p(t+1)$ lies in a measurable set $S$ with probability $\kappa_\alpha(p(t),S)$, the SAMBA transition probability;
--   2. with probability $1$, $p_{a^\star}(t)\to1$ as $t\to\infty$;
--   3. $Q:=\sum_{t=0}^\infty\mathbb P\big(p_{a^\star}(t)\le\tfrac12\big)<\infty$;
--   4. for every $T\ge1$,
--   $$
--   \mathcal Rg(T)\le\frac{N}{\alpha\Delta}\log T+Q .\qquad(3)
--   $$
--
--   SAMBA, a policy-gradient algorithm with a fixed learning rate, converges to the optimal arm and has logarithmic regret, the order of the Lai–Robbins lower bound.
--
--   **Formalization Note** $Q$ is a sum in $[0,\infty]$; its finiteness is clause 3 and the bound uses its real value. The regret is the first expression of (5).
--
--   Differences from the source:
--
--   - reading: α ∈ (0, 1) is fixed in the algorithm box (p.4), not in the statement → hypotheses 0 < α and α < 1; reason: SAMBA is run with α ∈ (0, 1); for α ≥ 1 the update leaves the simplex (Lemma 10)
--   - reading: p_a := 1/N is fixed in the algorithm box (p.4), not in the statement → the run starts from the uniform vector; reason: the algorithm’s initialization; the regret bound is false at T = 1 for other starts
--   - generalization: α < ∆/(r⋆ − ∆), condition (2) → α (r⋆ − ∆) < ∆; reason: equivalent to (2) when r⋆ > ∆; also covers r⋆ = ∆, where the printed fraction is undefined
--   - generalization: the SAMBA process is a Markov chain → the conditional law of p(t + 1) given all randomness used before t is κ_α(p(t), ·); reason: a Markov property for the larger history implies it for the natural filtration of p
--   - encoding: Q := Σ_t P(p_{a⋆}(t) ≤ 1/2) < ∞ and the bound + Q → Q as a sum in [0, ∞], clause Q < ⊤, bound with Q.toReal; reason: a real tsum of a divergent series would be 0
--   - encoding: time t = 1, …, T in the algorithm box → time from 0, as in (5) and (6); reason: same process
--   - encoding: the bound (3) for T with log T defined → for every T ≥ 1; reason: log 0 is undefined; at T = 0 both sides are trivially 0 ≤ Q, so only an undefined case is excluded
--   - generalization: the arm is drawn with distribution p(t) (p.4) using an independent uniform (p.7) → any jointly measurable rule draw(p, u) with λ{u ∈ [0, 1] : draw(p, u) = a} = p_a on the simplex; reason: every such rule gives the same law of the process; the inverse-CDF rule is one instance
--   - generalization: the leading arm is chosen at random among the maximizers of p(t) (p.7), distribution unspecified → any measurable rule lead(p, v) that returns a maximizer of p, fed by an independent uniform v; reason: the uniform choice among maximizers is one instance
--   - reading: rewards R_a(t) are independent Bernoulli(r_a) (p.6); the policy uses an independent uniform (p.7); ties are broken at random (p.7) → the arm uniforms, tie-break uniforms and rewards over all times are mutually independent; rewards are {0, 1}-valued almost surely; reason: the paper’s independent randomization, made explicit
--   - encoding: a finite set of N arms → a Fintype with at least two elements; reason: for N = 1 the gap ∆ is a maximum over the empty set; only an undefined case is excluded
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Theorem 1, p.4, eqs. (2), (3); algorithm box, p.4; regret (5), p.7

import Mathlib
import Definitions.Def_SambaPG_regret
import Definitions.Def_SambaPG_IsDrawRule
import Definitions.Def_SambaPG_IsLeaderRule
import Definitions.Def_SambaPG_sambaKernel
import Definitions.Def_SambaPG_historyFiltration

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SambaPG

/-- **Theorem 1 (SAMBA: Markov chain, almost-sure convergence, logarithmic regret).**
Denisov & Walton, *Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits*,
arXiv:2007.10229v3, Theorem 1, p.4, eqs. (2), (3); algorithm box, p.4; regret (5), p.7.

Consider a Bernoulli bandit with `N ≥ 2` arms, means `r_a ∈ [0, 1]` and a unique optimal arm `a⋆`,
and run SAMBA with learning rate `α ∈ (0, 1)` from the uniform vector `p_a(0) = 1/N`. If
`α < ∆/(r⋆ − ∆)` (2), then
1. the SAMBA process `(p(t) : t ∈ ℤ₊)` is a Markov chain: given the history up to time `t`,
   `p(t + 1)` falls in a measurable set `S` with probability `κ_α(p(t), S)`, the SAMBA transition
   probability (`sambaKernel`);
2. with probability `1`, `p_{a⋆}(t) → 1` as `t → ∞`;
3. `Q := Σ_{t=0}^∞ P(p_{a⋆}(t) ≤ 1/2) < ∞`;
4. `Rg(T) ≤ (N/(α∆)) log T + Q` for every `T ≥ 1` (3).

**Formalization Note.** Condition (2) is written `α (r⋆ − ∆) < ∆`: the same condition when
`r⋆ > ∆`, and meaningful also when `r⋆ = ∆`, where the printed fraction is undefined.
`α ∈ (0, 1)` and the uniform start come from the algorithm box on p.4. `Q` is a sum in `[0, ∞]`, its
finiteness is clause 3, and the bound uses its real value. The draw rule and the tie-breaking rule
are arbitrary (`IsDrawRule`, `IsLeaderRule`); the history filtration contains all randomness used
before time `t`. -/
theorem theorem_1 {A : Type*} [Fintype A] [DecidableEq A] (B : BernoulliBandit A)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (ξ : SambaNoise B μ)
    {draw lead : (A → ℝ) → ℝ → A} (hdraw : IsDrawRule draw) (hlead : IsLeaderRule lead)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (h2 : α * (B.rStar - B.gap) < B.gap) :
    let N : ℝ := Fintype.card A
    let p₀ : A → ℝ := fun _ => 1 / N
    let p : ℕ → Ω → A → ℝ := sambaRun ξ α draw lead p₀
    let Q : ℝ≥0∞ := ∑' t : ℕ, μ {ω | p t ω B.aStar ≤ 1 / 2}
    (∀ (t : ℕ) (S : Set (A → ℝ)), MeasurableSet S →
      μ[fun ω => S.indicator (1 : (A → ℝ) → ℝ) (p (t + 1) ω) | historyFiltration ξ t]
        =ᵐ[μ] fun ω => sambaKernel B α lead (p t ω) S) ∧
    (∀ᵐ ω ∂μ, Tendsto (fun t => p t ω B.aStar) atTop (𝓝 1)) ∧
    Q < ⊤ ∧
    ∀ T : ℕ, 1 ≤ T →
      regret ξ α draw lead p₀ T ≤ N / (α * B.gap) * Real.log T + Q.toReal := by sorry

end SambaPG
