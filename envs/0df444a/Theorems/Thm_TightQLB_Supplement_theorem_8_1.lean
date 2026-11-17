-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_8_1
-- name    : TightQLB.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:28:52.333543+00:00
-- url     : https://prove2.me/theorems/231c0181-df4c-4016-9480-534417980d45
-- title:
--   Theorem 8.1 — Hadamard products of states with uniform magnitudes: trace distance $\le\frac\pi3\sqrt{m/N}+\sqrt2m/\sqrt N$ with $m+1+O(\sqrt{N/m})$ queries
-- statement:
--   Let $N=2^n$, let $|\alpha\rangle,|\beta\rangle\in\mathbb C^N$ satisfy $|\alpha_z|=|\beta_z|=N^{-1/2}$ for all $z$, so that $|\alpha\circ\beta\rangle=\sqrt N\sum_z\alpha_z\beta_z|z\rangle$, and let $1\le m\le N/4$. With oracle access for state preparation and reflection to $|\alpha\rangle$ and $|\beta\rangle$, there is an algorithm, fixed independently of $\alpha$ and $\beta$, that makes $m$ preparations of $|\alpha\rangle$, one preparation of $|\beta\rangle$, and at most $\pi\sqrt{N/m}/2$ further queries, and outputs a state $\rho$ on $\mathbb C^N$ with
--
--   $$
--   \frac12\big\|\rho-|\alpha\circ\beta\rangle\langle\alpha\circ\beta|\big\|_1\le\frac\pi3\sqrt{\frac mN}+\frac{\sqrt2\,m}{\sqrt N}.
--   $$
--
--   For $N\ge8$ and $m=\lceil N^{1/3}\rceil$ this algorithm makes $O(N^{1/3})$ queries and has trace distance $O(N^{-1/6})$, with one absolute constant.
--
--   The direct approach needs about $\sqrt N$ reflections; keeping $m$ coherent copies of $|\alpha\rangle$ reduces the cost to $O(N^{1/3})$ while preserving the product phases.
--
--   **Formalization Note** The algorithm makes its $m+1$ preparations first and then applies fixed unitaries interleaved with $k$ reflections about $|\beta\rangle$ ($2k$ queries, $2k\le\pi\sqrt{N/m}/2$); its output is the reduced state of the output register. This is the shape of the paper's algorithm, and a special form of state-preparation and reflection access, so the existential statement is at least as strong as the source's.
--
--   Differences from the source:
--   - reading: "there is an algorithm that makes m preparations of |α⟩, one preparation of |β⟩, and at most π√(N/m)/2 further queries", with oracle access for state preparation and reflection → ∃ HadamardAlg fixed before α, β: m + 1 preparations, then fixed unitaries interleaved with k reflections about |β⟩ (2k queries, 2k ≤ π√(N/m)/2), output the reduced state of Y; reason: the paper's algorithm has this shape, and restricting the class of algorithms makes the existential statement stronger
--   - reading: "For N = 2ⁿ ≥ 8 and m = ⌈N^{1/3}⌉, the algorithm makes O(N^{1/3}) queries and the trace distance is O(N^{−1/6})" → one constant C chosen before n; for the same algorithm, m + 1 + 2k ≤ C N^{1/3} and the trace distance ≤ C N^{−1/6}; reason: O-notation for an absolute bound
--   - encoding: C^N → N = 2^n, registers of n qubits; reason: §3.1: N = 2^n throughout; step 3 of the algorithm adds n-bit registers
--   - encoding: N = 2^n, N^{1/3}, N^{−1/3}, √N → (2 : ℝ)^n with Real.rpow and Real.sqrt; reason: Lean convention; same values
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 8.1, pp. 73–74 (PDF pp. 76–77)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Hadamard
open QAlgorithms

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 8.1 (Hadamard products of states with uniform magnitudes)**, pp.73–74
(PDF pp.76–77).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let `|α⟩, |β⟩ ∈ C^N` satisfy `|α_z| = |β_z| = N^{−1/2}` for all `z`, so that
`|α ∘ β⟩ = √N Σ_z α_zβ_z|z⟩`, and let `1 ≤ m ≤ N/4`. Suppose that oracle access for state preparation
and reflection to `|α⟩` and `|β⟩` is given. Then there is an algorithm that makes `m` preparations
of `|α⟩`, one preparation of `|β⟩`, and at most `π√(N/m)/2` further queries, and outputs a state `ρ`
on `C^N` with `(1/2)‖ρ − |α ∘ β⟩⟨α ∘ β|‖₁ ≤ (π/3)√(m/N) + √2 m/√N`. For `N = 2ⁿ ≥ 8` and
`m = ⌈N^{1/3}⌉`, the algorithm makes `O(N^{1/3})` queries and the trace distance is `O(N^{−1/6})`."

**Formalization Note.**
* The algorithm is a `HadamardAlg n m k K`: fixed before `α, β`, it makes the `m` preparations of
  `|α⟩` and the one of `|β⟩`, and `k` reflections about `|β⟩` (`2k` further queries), with fixed
  unitaries in between; `ρ` is the reduced state of the output register. This shape is a special
  form of an algorithm with state-preparation and reflection access, so the existential is at
  least as strong as the source's.
* The `O(·)` clause is one absolute constant `C`, chosen before `n`, for the same algorithm: the
  total number of queries `m + 1 + 2k` is at most `C N^{1/3}` and the distance at most `C N^{−1/6}`.
* `N = 2^n`; `|α ∘ β⟩` is `hadamardProd` (the normalized product), and the trace distance is
  `traceDist`. -/
theorem theorem_8_1 :
    ∃ C : ℝ, ∀ n m : ℕ, 1 ≤ m → (m : ℝ) ≤ (2 : ℝ) ^ n / 4 →
      ∃ (k : ℕ) (K : Type) (_ : Fintype K) (_ : DecidableEq K) (A : HadamardAlg n m k K),
        (2 * k : ℝ) ≤ Real.pi * Real.sqrt ((2 : ℝ) ^ n / m) / 2 ∧
        (∀ α β : EuclideanSpace ℂ (Qubits n),
          (∀ z, ‖α z‖ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹) → (∀ z, ‖β z‖ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹) →
          traceDist (A.output α β)
              (Matrix.vecMulVec (hadamardProd α β) (star (hadamardProd α β))) ≤
            Real.pi / 3 * Real.sqrt (m / (2 : ℝ) ^ n) + Real.sqrt 2 * m / Real.sqrt ((2 : ℝ) ^ n)) ∧
        (8 ≤ (2 : ℝ) ^ n → m = ⌈((2 : ℝ) ^ n) ^ (1 / 3 : ℝ)⌉₊ →
          ((m + 1 + 2 * k : ℕ) : ℝ) ≤ C * ((2 : ℝ) ^ n) ^ (1 / 3 : ℝ) ∧
          ∀ α β : EuclideanSpace ℂ (Qubits n),
            (∀ z, ‖α z‖ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹) →
            (∀ z, ‖β z‖ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹) →
            traceDist (A.output α β)
                (Matrix.vecMulVec (hadamardProd α β) (star (hadamardProd α β))) ≤
              C * ((2 : ℝ) ^ n) ^ (-(1 / 6 : ℝ))) := by sorry

end TightQLB.Supplement
