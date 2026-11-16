-- Prove2me | Theorems.Thm_TargetedSamplers_Supplement_theorem_5_1
-- name    : TargetedSamplers.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:15:27.630963+00:00
-- url     : https://prove2.me/theorems/f4cfa497-9d8d-47c6-8c24-aa69c4b68c71
-- title:
--   Theorem 5.1 — targeted sampler from non-batch computability
-- statement:
--   There is a universal constant $c>1$ and, for every $\alpha,\beta\in(0,1)$, a constant $\gamma(\alpha,\beta)>0$ such that the following holds. Let $T,r,k:\mathbb N\to\mathbb N$ be polynomials with $r(n)\le T(n)k(n)$, let $\delta:\mathbb N\to(0,1)$, and assume that one-way functions exist. Let $f:\{0,1\}^n\times\{0,1\}^{r(n)}\to\{0,1\}^{k(n)}$ satisfy:
--
--   1. **Upper bound.** A deterministic algorithm, for every $x_1\in\{0,1\}^n$ and for a $(1-\delta)$ fraction of $x_2\in\{0,1\}^{r(n)}$, on input $(x_1,x_2,i)$ runs in time $T'(n)=T(n)k(n)$ and outputs $f(x_1\circ x_2)_i$.
--   2. **Non-batch computability.** For constants $\alpha,\beta\in(0,1)$, every randomized algorithm $A$ running in time $T'(n)\,k^\beta$ satisfies: for all but finitely many $x_1$, for at least a $(1-\delta)$ fraction of $x_2$, with probability at least $1/2$ over its randomness the output of $A(x_1\circ x_2)$ disagrees with $f(x_1\circ x_2)$ on at least an $\alpha$ fraction of the indices $i\in[k]$.
--
--   Then there is a
--   $$\big(k^{-\gamma(\alpha,\beta)},\,2\delta\big)\text{-targeted sampler against }T\text{-time algorithms}$$
--   with randomness complexity $r$, sample complexity $S\le k^c$, and total time $T\cdot k^c$ for printing all the samples.
--
--   The theorem turns a function whose bits are individually easy but whose whole output is hard to print into a targeted sampler with few samples, the first of the paper's three constructions.
--
--   **Formalization Note** A polynomial $T:\mathbb N\to\mathbb N$ is a function that agrees on $\mathbb N$ with a real polynomial. The randomized algorithms of the hypothesis run within $\lceil T k^{1+\beta}\rceil+K$ steps with as many coins, for every constant $K$; an output $\bot$ counts as disagreeing. The upper-bound algorithm runs within $T(n)k(n)+K$ steps for some constant $K$. At $k(n)=0$ the accuracy $k^{-\gamma}=+\infty$ is written $1$.
--
--   Differences from the source:
--   - reading: non-batch computability 'for all but 1 − δ fraction of x₂' (literally, hardness on a δ fraction) → hardness on at least a (1 − δ) fraction of x₂; reason: the section's own preamble states the hypothesis this way (p.43: 'The crucial point is that the hardness assumption holds for every x₁ and at least 1 − δ of x₂'), as do Theorem 1.7 (p.6) and the proof (p.45); the theorem sentence's 'all but' is a slip of the preamble's 'at least'
--   - encoding: k^{−Ω_{α,β}(1)}; universal c > 1 → k^{−γ(α,β)} with γ(α,β) > 0 a function of α, β only, chosen with c before T, r, k, δ, f; reason: standard reading of subscripted constants
--   - encoding: T, r, k polynomials → functions ℕ → ℕ that agree on ℕ with a real polynomial; reason: same instances (every polynomial function ℕ → ℕ, including integer-valued ones such as n(n − 1)/2)
--   - encoding: randomized algorithm running in time T′k^β → program halting within ⌈T k^{1+β}⌉ + K steps on every input and coin string of that length, for every constant K; ⊥ counts as disagreement; reason: the base HardAgainst convention: the class of algorithms is not shrunk
--   - encoding: upper-bound algorithm in time T′, input (x₁, x₂, i) → time T(n)k(n) + K for some constant K, input encInput [i] [x₁, x₂]; reason: an additive constant for the RAM's start-up cost; a fixed input encoding
--   - encoding: accuracy k^{−γ} at k(n) = 0 → 1; reason: the source's value is +∞; every pair of means in [0,1] is 1-close
--   - encoding: targeted sampler (Definition 1.2) with ϵ(T), δ(T′) → IsTargetedSampler with accuracy and error functions of n; T-time = T(n) + K steps for every K; reason: same instances; ϵ(T(n)) is a function of n
--   - encoding: time bounds → the base mission's budget (constant and polylogarithmic factors); real powers rounded up; reason: the base mission's convention for the log-cost RAM
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 5.1, pp.43–44 (pdf pp.45–46)

import Mathlib
import Definitions.Def_TargetedSamplers_Supplement_IsOneWay
import Definitions.Def_TargetedSamplers_Supplement_IsTargetedSampler

namespace TargetedSamplers.Supplement

/-- Theorem 5.1 (targeted sampler based on non-batch computability) (Chen, Doron, Ebtehaj, Tell,
Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, pp.43–44). There is a universal
constant `c > 1` such that: let `T, r, k : ℕ → ℕ` be polynomials with `r(n) ≤ T(n) · k(n)`; assume
that one-way functions exist, and that for `δ : ℕ → (0, 1)` there is
`f : {0,1}ⁿ × {0,1}^{r(n)} → {0,1}^{k(n)}` with

* *upper bound:* a deterministic algorithm that, for all `x₁ ∈ {0,1}ⁿ` and a `(1 − δ)` fraction of
  `x₂`, given `(x₁, x₂, i)` runs in time `T′(n) = T(n) · k(n)` and outputs `f(x₁ ∘ x₂)_i`;
* *non-batch computability:* constants `α, β ∈ (0, 1)` such that every randomized algorithm `A`
  running in time `T′(n) · k^β` satisfies: for all but finitely many `x₁`, for a `(1 − δ)` fraction
  of `x₂`, with probability at least `1/2` over its randomness the output of `A(x₁ ∘ x₂)` disagrees
  with `f(x₁ ∘ x₂)` on at least an `α` fraction of the indices `i ∈ [k]`.

Then there is a `(k^{−Ω_{α,β}(1)}, 2δ)`-targeted sampler against `T`-time algorithms with sample
complexity `S ≤ k^c` and randomness complexity `r`, printing all its samples in time `T · k^c`.

**Formalization Note** `Ω_{α,β}(1)` is `γ(α, β) > 0`, a function of `α, β` only, chosen with `c`
before `T, r, k, δ, f`. A polynomial `T : ℕ → ℕ` is a function that agrees on `ℕ` with a real polynomial (this covers
integer-valued polynomials such as `n(n − 1)/2`).
"For all but `1 − δ` fraction of `x₂`" (non-batch computability) is read as "for at least a
`(1 − δ)` fraction of `x₂`", as in Theorem 1.7 and as the proof uses it (p.45). The randomized
algorithms of the hypothesis run in time exactly `⌈T k^{1+β}⌉ + K` with as many coins, for every
constant `K`; an output `⊥` counts as disagreeing. The upper-bound algorithm runs in time
`T(n) k(n) + K` for some constant `K`, on input `encInput [i] [x₁, x₂]`. At `k(n) = 0` the accuracy
`k^{−γ}` is `+∞` and is written `1` (every pair of means is `1`-close). The sampler gets `x₁` as input
and `r(n)` random bits; its printing time is `budget`. -/
theorem theorem_5_1 : ∃ c : ℝ, 1 < c ∧ ∃ γ : ℝ → ℝ → ℝ,
    (∀ α β : ℝ, 0 < α → α < 1 → 0 < β → β < 1 → 0 < γ α β) ∧
    ∀ T r k : ℕ → ℕ, (∃ p : Polynomial ℝ, ∀ n, (T n : ℝ) = p.eval (n : ℝ)) →
      (∃ p : Polynomial ℝ, ∀ n, (r n : ℝ) = p.eval (n : ℝ)) →
      (∃ p : Polynomial ℝ, ∀ n, (k n : ℝ) = p.eval (n : ℝ)) →
      (∀ n, r n ≤ T n * k n) →
    ∀ δ : ℕ → ℝ, (∀ n, 0 < δ n ∧ δ n < 1) →
    ∀ f : List Bool → List Bool → List Bool,
      (∀ x₁ x₂ : List Bool, x₂.length = r x₁.length → (f x₁ x₂).length = k x₁.length) →
      OWFExist →
      (∃ (F : Program) (K : ℕ), ∀ x₁ : List Bool,
        1 - δ x₁.length ≤ coinProb (r x₁.length) (fun x₂ => ∀ i : ℕ, i < k x₁.length →
          F.RunsIn (Tapes.ofInput (encInput [i] [x₁, x₂])) (T x₁.length * k x₁.length + K)
            (some [(f x₁ x₂).getD i false]))) →
    ∀ α β : ℝ, 0 < α → α < 1 → 0 < β → β < 1 →
      (∀ (K : ℕ) (A : Program),
        (∀ x₁ x₂ ρ : List Bool, x₂.length = r x₁.length →
          ρ.length = ⌈(T x₁.length : ℝ) * k x₁.length * (k x₁.length : ℝ) ^ β⌉₊ + K →
          ∃ v, A.RunsIn ⟨x₁ ++ x₂, ρ, [], noOracle⟩
            (⌈(T x₁.length : ℝ) * k x₁.length * (k x₁.length : ℝ) ^ β⌉₊ + K) v) →
        {x₁ : List Bool | ¬ (1 - δ x₁.length ≤ coinProb (r x₁.length) (fun x₂ =>
          1 / 2 ≤ coinProb (⌈(T x₁.length : ℝ) * k x₁.length * (k x₁.length : ℝ) ^ β⌉₊ + K)
            (fun ρ => ∀ out : List Bool, A.Outputs ⟨x₁ ++ x₂, ρ, [], noOracle⟩ (some out) →
              α * k x₁.length ≤
                ((List.range (k x₁.length)).countP fun i => decide (out[i]? ≠ (f x₁ x₂)[i]?)))))}.Finite) →
    ∃ samp : List Bool → List Bool → List (List Bool),
      IsTargetedSampler samp r T T
        (fun n => if k n = 0 then 1 else (k n : ℝ) ^ (-γ α β)) (fun n => 2 * δ n) ∧
      (∀ x y : List Bool, y.length = r x.length → ((samp x y).length : ℝ) ≤ (k x.length : ℝ) ^ c) ∧
      ∃ (P : Program) (K k' : ℕ), ∀ x y : List Bool, y.length = r x.length →
        P.RunsIn ⟨x, y, [], noOracle⟩
          (budget K k' ⌈(T x.length : ℝ) * (k x.length : ℝ) ^ c⌉₊ x.length)
          (some (samp x y).flatten) := by sorry

end TargetedSamplers.Supplement
