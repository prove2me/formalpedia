-- Prove2me | Theorems.Thm_PolySampIso_proposition_8
-- name    : PolySampIso.proposition_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:18.321367+00:00
-- url     : https://prove2.me/theorems/e5ae487c-3627-48ce-b12e-568a763a428a
-- title:
--   Proposition 8, p.50 — Algorithm 7 is a (3, δ)-χ²-to-TV oracle for π_t in time O(Kτmn^{ω−1})
-- statement:
--   There are constants $C_1,C>0$ such that the following holds, where Algorithm 7 uses $N=\lceil C_1n\tau\rceil$. Let $X$ be a nonempty bounded polytope with $m$ constraints in $\mathbb R^n$, $t\ge0$, $\delta\in(0,\tfrac12)$, $\tau\in\mathbb N$ with $\tau\ge C\log(m/\delta)$, and
--
--   $$K=\Big\lceil32\min\Big\{m\tau,1+\frac\tau t\Big\}\log\frac1\delta\Big\rceil\qquad(\tau/0=+\infty).$$
--
--   1. Algorithm 7 (LLTProxMRW$(\cdot,\tau,t,\delta)$), as a function of its input $x_0$, is a $(3,\delta)$-$\chi^2$-to-TV oracle for $\pi_t$: if $\chi^2(\mathrm{Law}(x_0)\|\pi_t)\le3$ then its output $x$ satisfies $\mathrm{TV}(\mathrm{Law}(x),\pi_t)\le\delta$.
--   2. For every $\varepsilon>0$ there are a program for the real RAM with Gaussian and exponential samples and a constant $C_2$ such that on input $\delta,x_0\in X,A,b,t,\tau$ the program halts on every realization of its randomness after at most $C_2K\tau mn^{\omega-1+\varepsilon}$ operations, and its output has exactly the law of Algorithm 7's output.
--
--   Here $\omega$ is the exponent of square matrix multiplication. This is the sampler for each cooled measure; with $\tau=O(\log(m/\delta))$ its total cost is $m\,\mathrm{polylog}$ iterations of $\tilde O(mn^{\omega-1})$.
--
--   Differences from the source:
--   - reading: N ← ⌈Cnτ⌉, C the constant from Lemma 34 (Algorithm 7, line 2) → ∃ C₁ > 0, chosen with C before all instance data, and N = ⌈C₁nτ⌉; reason: Lemma 34's constant is itself existential, so Algorithm 7 is fixed once such a constant is fixed
--   - encoding: K := ⌈32 min{mτ, 1 + τ/t} log(1/δ)⌉ at t = 0 → K = ⌈32mτ log(1/δ)⌉ at t = 0; reason: τ/0 = +∞ in the paper; Lean's τ/0 = 0 would change K
--   - encoding: (3, δ)-χ²-to-TV oracle for πt (Definition 8) → IsChiSqToTVOracle: the kernel of Algorithm 7 is Markov, maps X to X, and TV(νO, π_t) ≤ δ for every probability ν with χ²(ν∥π_t) ≤ 3; reason: kernel form of Definition 8
--   - reading: runs in time O(Kτmn^{ω−1}) (in the real RAM of §2.1) → ∀ ε > 0 ∃ one Admissible program of PolySampIso.Machine and C₂ > 0, before all inputs: on every pair of streams it halts with work ≤ C₂·K·τ·m·n^{ω−1+ε}, its output map is measurable and its output law equals Algorithm 7's kernel at x₀; reason: the paper names the model without an instruction list; ω = OAI…omega ℝ is an infimum that need not be attained
--   - encoding: τ ∈ N → τ ≥ 1; reason: the paper's N starts at 1
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Proposition 8, p.50 (PDF p.52); Algorithm 7, p.48; Lemma 33, p.47

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PolySampIso_Machine
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_ChiSqToTVOracle
import Definitions.Def_PolySampIso_LLTProxMRW

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Proposition 8** (Algorithm 7 is a `(3, δ)`-χ²-to-TV oracle for `π_t`, in time `O(Kτmn^{ω−1})`).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Proposition 8, p.50 (PDF p.52):

"Proposition 8. Let t ≥ 0, δ ∈ (0, 1/2), let πt be defined as in (43). Further, suppose τ ∈ N
satisfies, for an absolute constant C > 0, and K := ⌈32 min{mτ, 1 + τ/t} log(1/δ)⌉, τ ≥ C log(m/δ).
Then Algorithm 7, as a function of its input x0, is a (3, δ)-χ2-to-TV oracle for πt that runs in
time O(Kτmn^{ω−1})."

**Formalization Note.**
* `C₁` is the constant of Algorithm 7's line 2 (`N = ⌈C₁nτ⌉`, "the constant from Lemma 34") and
  `C` the absolute constant of the hypothesis `τ ≥ C log(m/δ)`; both are chosen before all instance
  data. `K = alg7Iters m τ t δ`, with the paper's `τ/0 = +∞` at `t = 0`.
* Oracle clause: the Markov kernel `lltProxMRW A b C₁ τ t δ` of Algorithm 7 is a
  `(3, δ)`-χ²-to-TV oracle for `π_t = cooled A b t` (Definition 8).
* Time clause, in the machine `PolySampIso.Machine`: for every `ε > 0` one `Admissible` program and
  one constant `C₂`, chosen before all inputs. The input is `δ` in cell `0`, `x₀ ∈ X` in the `x₀`
  slot, then `A`, `b`, and `t, τ` as tail scalars (`inputState`). On every pair of streams it halts
  with work `≤ C₂·K·τ·m·n^{ω−1+ε}`, its output map is measurable, and its output law is the
  Algorithm 7 kernel at `x₀`. `ω = OAI.MatrixMultiplication.Arithmetic.omega ℝ`, read with `ε` as
  in Theorem 2.
* `τ ∈ N` is `τ ≥ 1`. The standing assumption of §2.3 is kept. -/
theorem proposition_8 :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C : ℝ, 0 < C ∧
      (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), StandingAssumption A b →
        0 < n → ∀ t δ : ℝ, 0 ≤ t → 0 < δ → δ < 1 / 2 →
        ∀ τ : ℕ, 1 ≤ τ → C * Real.log (m / δ) ≤ τ →
          IsChiSqToTVOracle (polytope A b) (lltProxMRW A b C₁ τ t δ) (cooled A b t) 3 δ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ P : Program, Admissible P ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
        ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), StandingAssumption A b →
          0 < n → ∀ t δ : ℝ, 0 ≤ t → 0 < δ → δ < 1 / 2 →
          ∀ τ : ℕ, 1 ≤ τ → C * Real.log (m / δ) ≤ τ → ∀ x₀ ∈ polytope A b,
            let ω := OAI.MatrixMultiplication.Arithmetic.omega ℝ
            let s₀ := inputState ![δ, 0, 0] x₀ A b [t, (τ : ℝ)]
            (∀ ωs : Streams, ∃ k, (run P s₀ ωs k).halted = true ∧
              ((run P s₀ ωs k).work : ℝ) ≤
                C₂ * alg7Iters m τ t δ * τ * m * (n : ℝ) ^ (ω - 1 + ε)) ∧
            Measurable (finalOutput n P s₀) ∧
            tape.map (finalOutput n P s₀) = lltProxMRW A b C₁ τ t δ x₀) := by sorry

end PolySampIso
