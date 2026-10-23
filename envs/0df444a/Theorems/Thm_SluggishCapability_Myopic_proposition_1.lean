-- Prove2me | Theorems.Thm_SluggishCapability_Myopic_proposition_1
-- name    : SluggishCapability.Myopic.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:25.544929+00:00
-- url     : https://prove2.me/theorems/be7c3905-c186-4966-87a0-820cdbeada37
-- title:
--   Proposition 1, pp. 10–11, with ε < 1/2 in part (i) — a myopic sluggish agent's lowest long-run capability is at most 2µ − 1, attained by a perturbed two-state cycle
-- statement:
--   Let $\mu \ge 1$ be an integer and $\varepsilon \in (0, 1)$. A trainer commits to a feasible training program $(P, f)$: a stochastic irreducible transition matrix $P$ on a finite set of states $S$ and challenge levels $f : S \to \mathbb{N}$ whose invariant distribution $\lambda_P$ satisfies $\sum_s \lambda_P(s) f(s) \le \mu + \varepsilon$. A sluggish agent adjusts capability by the myopic rule (2): one unit up if the challenge exceeds its capability, one unit down (but not below $0$) if it falls short, and no change otherwise. The **lowest long-run capability** $m^*$ is the lowest value capability takes beyond a sufficiently large period.
--
--   **(i)** If $\varepsilon < 1/2$, then for every feasible program
--   $$m^* \le 2\mu - 1 .$$
--   Precisely: for every truncation level $M \ge \max_s f(s)$ and every recurrent state $x$ of the extended (capability, state) chain, some state reachable from $x$ (hence in the recurrent class of $x$) has capability at most $2\mu - 1$.
--
--   **(ii)** The bound is attained. There is $\beta_0 \in [0,1)$ such that for every $\beta \in (\beta_0, 1)$ the two-state program with states $L, H$,
--   $$\Pr(L \to H) = 1,\quad \Pr(H \to L) = \beta,\quad \Pr(H \to H) = 1 - \beta,\qquad f(L) = 0,\ f(H) = 2\mu,$$
--   is feasible, and for every $M \ge 2\mu$ its extended chain has exactly the recurrent states $(2\mu - 1, L)$ and $(2\mu, H)$, has an invariant distribution, and every invariant distribution puts mass $\frac{1}{1+\beta}$ on $(2\mu, H)$ and $\frac{\beta}{1+\beta}$ on $(2\mu - 1, L)$. Thus $m^* = 2\mu - 1$ from every initial capability, and as $\beta \to 1$ the invariant capability distribution assigns probability $\tfrac12$ to each of $m = 2\mu$ and $m = 2\mu - 1$.
--
--   The result shows that against a sluggish agent a trainer with average-intensity budget $\mu + \varepsilon$ can sustain a long-run capability close to $2\mu$, about twice what the same budget sustains for a flexible agent.
--
--   **Formalization Note** (1) Part (i) is posed with $\varepsilon < 1/2$, which the paper does not state: it is false for $\varepsilon > 1/2$. Counterexample: $\mu = 1$, $\varepsilon = 3/5$, the same two-state shape with $\beta = 7/8$ and $f(H) = 3$, $f(L) = 0$; then $\lambda_P = (7/15, 8/15)$, the average challenge is $8/5 = \mu + \varepsilon$, and the only recurrent states are $(2, L)$ and $(3, H)$, so $m^* = 2 > 2\mu - 1$. The paper says $\varepsilon$ can be arbitrarily close to zero and treats it as negligible. (2) "Lowest long-run capability" is read through recurrent states of the finite extended chain on `Fin (M + 1) × S`; quantifying over every $M \ge \max f$ covers every initial capability, and over every recurrent state covers every class a path can be absorbed in. (3) "In the $\beta \to 1$ limit … $\tfrac12$" is stated through the exact masses $\frac{1}{1+\beta}$ and $\frac{\beta}{1+\beta}$. (4) Feasibility asks for some invariant distribution satisfying (1); it is unique by irreducibility. Index `0` is $L$, `1` is $H$; $2\mu - 1$ is natural-number subtraction ($\mu \ge 1$).
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), pp. 10–11, Proposition 1 (proof pp. 17–20)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace SluggishCapability.Myopic

/-- **Proposition 1**, pp. 10–11, with `ε < 1/2` added to part (i).
(i) For every feasible training program `(P, f)` on any finite state set, every truncation
`M ≥ max f` and every recurrent state `x` of the extended (capability, state) chain, the
recurrent class of `x` contains a state of capability at most `2µ − 1`: the lowest long-run
capability is at most `2µ − 1`.
(ii) For all `β` in some interval `(β₀, 1)`, the two-state program (index `0` is `L`, `1` is `H`)
`Pr(L → H) = 1`, `Pr(H → L) = β`, `f(L) = 0`, `f(H) = 2µ` is feasible, its extended chain has
exactly the recurrent states `(2µ − 1, L)` and `(2µ, H)`, it has an invariant distribution, and
every invariant distribution puts mass `1/(1 + β)` on `m = 2µ` and `β/(1 + β)` on `m = 2µ − 1`
(both tend to `1/2` as `β → 1`). -/
theorem proposition_1 (μ : ℕ) (hμ : 1 ≤ μ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (ε < 1 / 2 →
      ∀ (S : Type) [Fintype S] [DecidableEq S] (P : Matrix S S ℝ) (f : S → ℕ),
        IsFeasibleProgram P f μ ε → ∀ M : ℕ, (∀ s, f s ≤ M) →
        ∀ x : Fin (M + 1) × S, IsRecurrentState (extKernel P f M) x →
          ∃ y : Fin (M + 1) × S, Reaches (extKernel P f M) x y ∧ (y.1 : ℕ) ≤ 2 * μ - 1) ∧
    (∃ β₀ : ℝ, 0 ≤ β₀ ∧ β₀ < 1 ∧ ∀ β : ℝ, β₀ < β → β < 1 →
      IsFeasibleProgram (twoStateP β) (twoStateF μ) μ ε ∧
      ∀ M : ℕ, 2 * μ ≤ M →
        (∀ x : Fin (M + 1) × Fin 2,
          IsRecurrentState (extKernel (twoStateP β) (twoStateF μ) M) x ↔
            (((x.1 : ℕ) = 2 * μ - 1 ∧ x.2 = 0) ∨ ((x.1 : ℕ) = 2 * μ ∧ x.2 = 1))) ∧
        (∃ ν : Fin (M + 1) × Fin 2 → ℝ,
          IsStationary (extKernel (twoStateP β) (twoStateF μ) M) ν) ∧
        ∀ ν : Fin (M + 1) × Fin 2 → ℝ,
          IsStationary (extKernel (twoStateP β) (twoStateF μ) M) ν →
          ∀ x : Fin (M + 1) × Fin 2,
            ((x.1 : ℕ) = 2 * μ → x.2 = 1 → ν x = 1 / (1 + β)) ∧
            ((x.1 : ℕ) = 2 * μ - 1 → x.2 = 0 → ν x = β / (1 + β))) := by sorry

end SluggishCapability.Myopic
