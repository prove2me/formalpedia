-- Prove2me | Theorems.Thm_StaticCalendar_theorem_1
-- name    : StaticCalendar.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:04.281432+00:00
-- url     : https://prove2.me/theorems/a4b32d10-0f8a-4888-b51e-2e25eb9bda77
-- title:
--   Theorem 1 — the randomized LP calendar earns at least $\Delta^{APX}\ge1-1/e$ of the LP optimum (corrected: (10) at $\lfloor b\rfloor$)
-- statement:
--   Consider the assortment and pricing problem with $n$ items, $m$ prices, a downward-closed family of assortments, stationary demand with quantities in $[0,1]$, $T$ periods, and inventories $1\le b_i\le T$. Assume static substitution, and assume either that demand is $\{0,1\}$-valued or Assumption 2. Write $\underline b=\min_ib_i$ and
--
--   $$
--   \Delta^{APX}=\frac{\mathbb E[\min\{\mathrm{Bin}(T,\underline b/T),\underline b\}]}{\underline b}.
--   $$
--
--   1. Algorithm 1, run on a solution $x$ of CDLP-S, earns expected revenue at least $\Delta^{APX}$ times the LP objective at $x$:
--
--   $$
--   \mathbb E[\text{revenue of Algorithm 1}]\ \ge\ \Delta^{APX}\cdot\mathsf{OPT}_{\mathrm{LP}}\quad\text{for optimal }x. \tag{9}
--   $$
--
--   2. For $1\le b\le T$,
--
--   $$
--   \Delta^{APX}(T,b)\ \ge\ 1-\frac{\lfloor b\rfloor^{\lfloor b\rfloor}}{\lfloor b\rfloor!}e^{-\lfloor b\rfloor}. \tag{10}
--   $$
--
--   3. $\Delta^{APX}=1-O(1/\sqrt b)$ with a constant independent of $T$; $\Delta^{APX}(T,\cdot)$ is non-decreasing on $[1,T]$; and $1-1/e\le\Delta^{APX}\le1$.
--
--   This is the paper's first main result: a static randomized calendar, with no adaptivity to inventories, attains a tight non-asymptotic fraction of the LP upper bound. The revenue on the left of (9) is the expectation of the sequential revenue with inventory truncation, not a virtual or per-item proxy.
--
--   Differences from the source:
--   - correction: (10) with $\underline b!$, $\underline b^{\underline b}$, $e^{-\underline b}$ → (10) with $\lfloor b\rfloor$ throughout; reason: $\underline b!$ is undefined for fractional inventories, and the $\Gamma$ reading is false: $n=m=1$, $p_1=1$, $T=10$, $b_1=1.5$, Bernoulli$(0.15)$ demand, $x=1$ on $\{(1,1)\}$ give $\Delta^{APX}=0.68732<1-1.5^{1.5}e^{-1.5}/\Gamma(2.5)=0.69164$; the floor equals the printed form for integer $\underline b$ and is the form of Proposition EC.1, p.ec14
--   - generalization: $x^*$ an optimal solution of CDLP-S → any feasible $x$; reason: feasibility, constraints (6)–(8), is all the argument uses; an optimal solution is feasible
--   - generalization: $\underline b=\min_ib_i$ in (9) → any $b_0\in[1,\min_ib_i]$; reason: $b_0=\min_ib_i$ is the source
--   - reading: "$\Delta^{APX}=1-O(1/\sqrt{\underline b})$, and increases from $1-1/e$ to $1$ as $\underline b\to\infty$ (regardless of $T$)" → $\exists C$ uniform in $T,b$ with $\Delta^{APX}\ge1-C/\sqrt b$; monotone on $[1,T]$; $1-1/e\le\Delta^{APX}\le1$; reason: the gloss is informal; these clauses give the convergence to $1$ uniformly in $T$ and the monotonicity in $b$
--   - encoding: "with Assumption 2 needed if demand is fractional" → hypothesis `Assumption2 I ∨ BinaryDemand I`; reason: integral instances, $b_i\in\mathbb N$ with $\{0,1\}$ demand, are instances of the real-inventory model
--   - encoding: Assumption 2 as a ratio of expectations → the cross-multiplied form `Assumption2`; reason: equivalent when both means are positive; the ratio is undefined otherwise and the product form reads $0\le0$
--   - encoding: demand laws on $[0,1]^{|S|}$; Algorithm 1 as a procedure → laws on $\mathbb R^{[n]\times[m]}$ vanishing off $S$; the product over periods of the one-period mixture law; reason: same law of the run
--   - encoding: $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$ → the explicit binomial sum `binomMinExp`; reason: the definition of the expectation of a function of a binomial variable; same value
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Theorem 1, p.14; Theorem EC.1, p.ec8

import Mathlib
import Definitions.Def_StaticCalendar_Assumption2
import Definitions.Def_StaticCalendar_BinaryDemand
import Definitions.Def_StaticCalendar_IsLPFeasible
import Definitions.Def_StaticCalendar_lpObjective
import Definitions.Def_StaticCalendar_algRev
import Definitions.Def_StaticCalendar_deltaAPX

open MeasureTheory

namespace StaticCalendar

/-- Theorem 1, arXiv:1811.01077v5, p.14. Under static substitution and stationary demand:

1. (9) Algorithm 1 earns expected revenue at least `Δ^{APX} · OPT_LP`, with Assumption 2 needed if
   demand is fractional. Here `x` is any feasible solution of CDLP-S and `b₀` any number in
   `[1, minᵢ bᵢ]`; `x` optimal and `b₀ = minᵢ bᵢ` give (9).
2. (10) `Δ^{APX} ≥ 1 - ⌊b⌋^⌊b⌋ e^{-⌊b⌋}/⌊b⌋!`.
3. The gloss after (10): `Δ^{APX} = 1 - O(1/√b)` uniformly in `T`, and `Δ^{APX}` increases in `b`,
   from at least `1 - 1/e`, staying at most `1` (so it tends to `1` as `b → ∞`, regardless of `T`).

**Formalization Note.** (10) is printed with `b̲!`, `b̲^b̲`, `e^{-b̲}`. For fractional `b̲` the
factorial is undefined, and the `Γ` reading is false: at `T = 10`, `b = 1.5`,
`Δ^{APX} = 0.68732 < 1 - 1.5^{1.5} e^{-1.5}/Γ(2.5) = 0.69164`. The floor is the form of
Proposition EC.1, p.ec14, and agrees with the printed one for integer `b̲`. -/
theorem theorem_1 :
    (∀ {n m : ℕ} (I : DemandModel n m) (T : ℕ) (b : Fin n → ℝ),
      (∀ i, 1 ≤ b i) → (∀ i, b i ≤ T) → (Assumption2 I ∨ BinaryDemand I) →
      ∀ x : Assortment n m → ℝ, IsLPFeasible I T b x →
      ∀ b₀ : ℝ, 1 ≤ b₀ → (∀ i, b₀ ≤ b i) →
        deltaAPX T b₀ * lpObjective I T x ≤ algRev I x b T) ∧
    (∀ (T : ℕ) (b : ℝ), 1 ≤ b → b ≤ T →
      1 - (⌊b⌋₊ : ℝ) ^ ⌊b⌋₊ * Real.exp (-(⌊b⌋₊ : ℝ)) / (⌊b⌋₊.factorial : ℝ) ≤ deltaAPX T b) ∧
    (∃ C : ℝ, ∀ (T : ℕ) (b : ℝ), 1 ≤ b → b ≤ T → 1 - C / Real.sqrt b ≤ deltaAPX T b) ∧
    (∀ T : ℕ, MonotoneOn (deltaAPX T) (Set.Icc 1 (T : ℝ))) ∧
    (∀ (T : ℕ) (b : ℝ), 1 ≤ b → b ≤ T →
      1 - Real.exp (-1) ≤ deltaAPX T b ∧ deltaAPX T b ≤ 1) := by sorry

end StaticCalendar
