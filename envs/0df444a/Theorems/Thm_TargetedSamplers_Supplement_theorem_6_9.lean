-- Prove2me | Theorems.Thm_TargetedSamplers_Supplement_theorem_6_9
-- name    : TargetedSamplers.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:16:30.752207+00:00
-- url     : https://prove2.me/theorems/675ddf1c-a2a0-4569-8289-3d3c3da44fb3
-- title:
--   Theorem 6.9 — targeted hitter from hardness of uniform circuits with low-degree gates
-- statement:
--   There is a universal constant $c$ such that the following holds. Let $T,r,w,d:\mathbb N\to\mathbb N$ be time-constructible, with $w$ always a power of $2$, $T(n)\ge\max\{d(n),w(n)\}$ and $\bar T:=w(n)T(n)\ge n+r(n)$; let $\epsilon\in(0,1)$ be a small enough constant and $\delta:\mathbb N\to(0,1)$. Assume that there is a highly uniform family $\{C_{n+r(n)}:\{0,1\}^{n+r(n)}\to\{0,1\}^{w(n)}\}$ of $(d\times w)$-circuits with $(T^{\epsilon^2},\bar T)$-low-degree gates such that every randomized algorithm $A$ running in time $(w+d)\cdot w^{c\epsilon}\cdot T^{c\epsilon^2}\cdot\widetilde O(\bar T)$ satisfies, for all but finitely many $x_1\in\{0,1\}^n$,
--   $$\Pr_{x_2\in\{0,1\}^{r(n)}}\Big[\Pr_A\big[A(x_1\circ x_2)=C_{n+r(n)}(x_1\circ x_2)\big]\ge\tfrac23\Big]<\delta.$$
--   Then there is a $(w^{-\Omega(\epsilon^2)},\delta)$-targeted hitter against $T$-time algorithms that runs in time $d\cdot w^2\cdot T^{1+c\epsilon}$, with randomness complexity $r(n)$, sample complexity $d\cdot w^2\cdot T^{c\epsilon}$ and output length $T^{\epsilon^3/c}\cdot w^{\epsilon^2/c}$.
--
--   This is the paper's main targeted-hitter construction: hardness of a structured function on most second halves of the input yields error reduction for one-sided-error algorithms with few samples.
--
--   **Formalization Note** $\widetilde O(X)$ in the hypothesis is $X(\log_2X+2)^c$; the accuracy is $w^{-\epsilon^2/c}$ and the output length $\lceil T^{\epsilon^3/c}w^{\epsilon^2/c}\rceil$.
--
--   Differences from the source:
--   - reading: a universal constant c → c chosen after the constants H hidden in Definition 6.1 (and before ϵ₀, T, r, w, d, ϵ, δ and the family); reason: the hypothesis' Õ(T̄) must absorb the time for printing the family's gate, whose constants are those of H; the brief fixes this order
--   - encoding: ϵ small enough; w^{−Ω(ϵ²)} → ∃ ϵ₀ > 0 after c, ∀ ϵ ∈ (0, ϵ₀); accuracy w^{−ϵ²/c} with the same c; reason: every bound of the statement weakens as c grows, so one constant is no restriction
--   - encoding: Õ(T̄) in the hypothesis → T̄·(log₂ T̄ + 2)^c; reason: the theorem's own constant
--   - encoding: randomized algorithm running in time t → program halting within ⌈t⌉ + K steps with as many coins, on every input x₁∘x₂ and coin string, for every constant K; reason: the base HardAgainst convention: the class of algorithms is not shrunk
--   - encoding: no fan-in restriction (footnote 39) → fan-in bound n + r(n), the number of child slots of a gate, so it never binds; reason: same instances
--   - encoding: family {C_{n+r(n)}} → indexed by n with input length n + r(n); the uniform programs receive 1ⁿ; reason: n + r(n) need not be injective in n
--   - encoding: output length T^{ϵ³/c}·w^{ϵ²/c} → ⌈T^{ϵ³/c}·w^{ϵ²/c}⌉; reason: a length is an integer
--   - encoding: time bounds → the base mission's budget (constant and polylogarithmic factors); real powers rounded up; reason: the base mission's convention for the log-cost RAM
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 6.9, p.57 (pdf p.59)

import Mathlib
import Definitions.Def_TargetedSamplers_Supplement_LowDegreeCircuit
import Definitions.Def_TargetedSamplers_Supplement_IsTargetedSampler
import Definitions.Def_TargetedSamplers_TimeConstructible

namespace TargetedSamplers.Supplement

/-- Theorem 6.9 (targeted hitter based on hardness of uniform circuits with low-degree gates) (Chen,
Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, p.57).
There is a universal constant `c` such that: let `T, r, w, d : ℕ → ℕ` be time-constructible, `w`
always a power of 2, `T(n) ≥ max{d(n), w(n)}`, and `T̄ := w(n) · T(n) ≥ n + r(n)`; let `ϵ ∈ (0, 1)` be
a small enough constant and `δ : ℕ → (0, 1)`. Assume a highly uniform family
`{C_{n+r(n)} : {0,1}^{n+r(n)} → {0,1}^{w(n)}}` of `(d × w)`-circuits with `(T^{ϵ²}, T̄)`-low-degree
gates such that for every randomized algorithm `A` running in time
`(w + d) · w^{c·ϵ} · T^{c·ϵ²} · Õ(T̄)`, for all but finitely many `x₁ ∈ {0,1}ⁿ`,
`Pr_{x₂ ∈ {0,1}^{r(n)}}[Pr_A[A(x₁ ∘ x₂) = C_{n+r(n)}(x₁ ∘ x₂)] ≥ 2/3] < δ`. Then there is a
`(w^{−Ω(ϵ²)}, δ)`-targeted hitter against `T`-time algorithms that runs in time
`d · w² · T^{1+c·ϵ}`, with randomness complexity `r(n)`, sample complexity `d · w² · T^{c·ϵ}` and
output length `T^{ϵ³/c} · w^{ϵ²/c}`.

**Formalization Note** The constants hidden in Definition 6.1 (`H`) are quantified first: `c` may
depend on them (the hypothesis' `Õ(T̄)` must absorb the time for printing the gate). Then `c > 0`, the
threshold `ϵ₀` of "`ϵ` small enough", and the same `c` gives the accuracy `w^{−ϵ²/c}` (`Ω(ϵ²)`): all
three bounds weaken as `c` grows, so one constant is no restriction. `Õ(X)` in the hypothesis is
`X · (log₂ X + 2)^c`. The randomized algorithms of the hypothesis run in time exactly that bound plus
`K`, with as many coins, for every constant `K`. The family is indexed by `n` with input length
`n + r(n)`; its gates have no fan-in restriction (footnote 39): the fan-in bound is the input length
`n + r(n)`, the number of child slots of a gate, so it never binds. The output length is `⌈T^{ϵ³/c} · w^{ϵ²/c}⌉`; the
hitter's running time is `budget`; real quantities are rounded up. -/
theorem theorem_6_9 : ∀ H : UnifConsts, ∃ c : ℝ, 0 < c ∧ ∃ ϵ₀ : ℝ, 0 < ϵ₀ ∧
    ∀ T r w d : ℕ → ℕ, TimeConstructible T → TimeConstructible r → TimeConstructible w →
      TimeConstructible d → (∀ n, ∃ e : ℕ, w n = 2 ^ e) → (∀ n, d n ≤ T n ∧ w n ≤ T n) →
      (∀ n, n + r n ≤ w n * T n) →
    ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 → ϵ < ϵ₀ →
    ∀ δ : ℕ → ℝ, (∀ n, 0 < δ n ∧ δ n < 1) →
    ∀ C : List Bool → List Bool,
      IsHighlyUniformLDFamily H (fun n => n + r n) C d w (fun n => n + r n)
        (fun n => (T n : ℝ) ^ (ϵ ^ 2))
        (fun n => w n * T n) →
      (∀ (K : ℕ) (A : Program),
        (∀ x₁ x₂ ρ : List Bool, x₂.length = r x₁.length →
          ρ.length = ⌈((w x₁.length + d x₁.length : ℕ) : ℝ) * (w x₁.length : ℝ) ^ (c * ϵ) *
              (T x₁.length : ℝ) ^ (c * ϵ ^ 2) * ((w x₁.length * T x₁.length : ℕ) : ℝ) *
              (Real.logb 2 (w x₁.length * T x₁.length : ℕ) + 2) ^ c⌉₊ + K →
          ∃ v, A.RunsIn ⟨x₁ ++ x₂, ρ, [], noOracle⟩
            (⌈((w x₁.length + d x₁.length : ℕ) : ℝ) * (w x₁.length : ℝ) ^ (c * ϵ) *
              (T x₁.length : ℝ) ^ (c * ϵ ^ 2) * ((w x₁.length * T x₁.length : ℕ) : ℝ) *
              (Real.logb 2 (w x₁.length * T x₁.length : ℕ) + 2) ^ c⌉₊ + K) v) →
        {x₁ : List Bool | ¬ (coinProb (r x₁.length) (fun x₂ =>
          2 / 3 ≤ coinProb (⌈((w x₁.length + d x₁.length : ℕ) : ℝ) * (w x₁.length : ℝ) ^ (c * ϵ) *
              (T x₁.length : ℝ) ^ (c * ϵ ^ 2) * ((w x₁.length * T x₁.length : ℕ) : ℝ) *
              (Real.logb 2 (w x₁.length * T x₁.length : ℕ) + 2) ^ c⌉₊ + K)
            (fun ρ => A.Outputs ⟨x₁ ++ x₂, ρ, [], noOracle⟩ (some (C (x₁ ++ x₂))))) <
          δ x₁.length)}.Finite) →
    ∃ samp : List Bool → List Bool → List (List Bool),
      IsTargetedHitter samp r
        (fun n => ⌈(T n : ℝ) ^ (ϵ ^ 3 / c) * (w n : ℝ) ^ (ϵ ^ 2 / c)⌉₊) T
        (fun n => (w n : ℝ) ^ (-(ϵ ^ 2 / c))) δ ∧
      (∀ x y : List Bool, y.length = r x.length →
        ((samp x y).length : ℝ) ≤
          d x.length * (w x.length : ℝ) ^ 2 * (T x.length : ℝ) ^ (c * ϵ)) ∧
      ∃ (P : Program) (K k : ℕ), ∀ x y : List Bool, y.length = r x.length →
        P.RunsIn ⟨x, y, [], noOracle⟩
          (budget K k ⌈d x.length * (w x.length : ℝ) ^ 2 * (T x.length : ℝ) ^ (1 + c * ϵ)⌉₊
            x.length)
          (some (samp x y).flatten) := by sorry

end TargetedSamplers.Supplement
