-- Prove2me | Theorems.Thm_QMultiMean_Supplement_theorem_4_10
-- name    : QMultiMean.Supplement.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:19:26.220105+00:00
-- url     : https://prove2.me/theorems/eb15c85a-5ead-4560-a6ac-8e21fd79b7f6
-- title:
--   Theorem 4.10 — phase-oracle lower bounds in all regimes, in $\ell_1$ and (times $d^{1/p-1}$) in $\ell_p$, $p\in(1,\infty]$
-- statement:
--   There is a constant $c>0$ with the following property. Let $d\in\mathbb N$ and $n,n'\ge1$, and consider a quantum algorithm that approximates the mean $\mu$ of any random variable with values in $[-1/4,1/4]^d$ using at most $n$ queries to $U_{\mathbb P}$ and at most $n'$ queries to $\mathcal P_X$. Let
--   $$f=\begin{cases}d,&\text{if } n'<d,\\[2pt] \max\{d/\sqrt n,\,d^2/n'\},&\text{if } n'\ge d\text{ and } n<d,\\[2pt] \max\{d^{3/2}/n,\,d^2/n'\},&\text{if } n'\ge d\text{ and } n\ge d.\end{cases}$$
--   Then:
--
--   1. there is an instance on which the output $\tilde\mu$ satisfies $\|\tilde\mu-\mu\|_1\ge c\,f$ with probability at least $2/3$;
--   2. for every $p\in(1,\infty)$ there is an instance on which $\|\tilde\mu-\mu\|_p\ge c\,d^{1/p-1}f$ with probability at least $2/3$;
--   3. there is an instance on which $\|\tilde\mu-\mu\|_\infty\ge c\,f/d$ with probability at least $2/3$ (the case $p=\infty$).
--
--   An instance is a distribution, a random variable with values in $[-1/4,1/4]^d$ and a quantum experiment $U_{\mathbb P}$. Together with Theorem 4.5 this determines the query complexity of phase-oracle mean estimation in every regime up to polylogarithmic factors.
--
--   **Formalization Note** One constant $c$ serves all three regimes and every $p$. The case $d=0$ is allowed and trivial.
--
--   Differences from the source:
--   - reading: "a quantum algorithm that finds an approximation µ̃ of the mean of any random variable with values in [−1/4,1/4]^d" (no formal model in the paper) → a family of PhaseEstimators, one per sample set Ω = Fin (N+1), fixed before the instance (uncontrolled U_P/U_P⁻¹, controlled P_X/P_X⁻¹); the adversary picks N, a PMF P, X with values in [−1/4,1/4]^d and a quantum experiment U_P meeting Definition 2.5 (P_X is determined by X); reason: the upper bounds' model; U_P is fixed by Definition 2.5 only on |0⟩, so the hard instance includes it
--   - reading: ‖µ̃ − µ‖₁ = Ω(f) with probability at least 2/3 → a universal constant c > 0 chosen first, and probability at least 2/3 that ‖µ̃ − µ‖₁ ≥ c·f; reason: standard reading of Ω, read literally as a lower bound holding with probability at least 2/3
--   - reading: using n queries to U_P and n′ queries to P_X → using at most that many, on every sample set; reason: fewer queries can always be padded with unused ones
--   - encoding: the lower bound d^{1/p−1}·f for ‖µ̃ − µ‖_p at p = ∞ → c·f/d ≤ supNorm(µ̃ − µ); reason: d^{1/∞−1} = d^{−1} and ‖·‖∞ is the published supNorm; same instances
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.27, Theorem 4.10

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_Supplement_phaseOracle
import Definitions.Def_QMultiMean_Supplement_PhaseCircuit
import Definitions.Def_QMultiMean_Supplement_lpNorm

set_option autoImplicit false

namespace QMultiMean.Supplement

open QMultiMean

/-- Theorem 4.10 of Cornelissen, Hamoudi, Jerbi, *Near-Optimal Quantum Algorithms for Multivariate
Mean Estimation*, arXiv:2111.09787v2, p.27: let `d ∈ ℕ`, `n, n′ ≥ 1`, and consider a quantum
algorithm that approximates the mean `µ` of any random variable with values in `[−1/4, 1/4]^d`
using `n` queries to `U_P` and `n′` queries to `P_X`. Then there exist instances such that, with
probability at least `2/3`, `‖µ̃ − µ‖₁ = Ω(f)` where `f = d` if `n′ < d`,
`f = max{d/√n, d²/n′}` if `n′ ≥ d` and `n < d`, and `f = max{d^{3/2}/n, d²/n′}` if `n′ ≥ d` and
`n ≥ d`. Moreover, `d^{1/p−1} f` is obtained in the same way as a lower bound for `‖µ̃ − µ‖_p`, for
all `p ∈ (1, ∞]`.

**Formalization Note.** `Ω(·)` is a universal constant `c > 0` chosen before every other
parameter. A quantum algorithm is a family of `PhaseEstimator`s, one for each sample set
`Ω = Fin (N+1)`, fixed before the instance (uncontrolled `U_P`/`U_P⁻¹` calls, controlled
`P_X`/`P_X⁻¹` calls, computational-basis measurement, classical output map). The adversary chooses
`N`, the probability mass function `P`, the random variable `X` with values in `[−1/4, 1/4]^d` (every
coordinate of every value) and a quantum experiment `U_P` meeting Definition 2.5; the phase oracle
`P_X` (Definition 2.7) is determined by `X`. "Error `Ω(f)` with probability at least `2/3`" is read
literally: the output satisfies `‖µ̃ − µ‖ ≥ c·f` with probability at least `2/3`. "Using `n` queries"
is "using at most `n` queries" on every sample set. `‖·‖₁` is `lpNorm 1`. `d = 0` is allowed (the
statement is then trivially true). One constant `c` serves all three cases and every `p`. Each norm clause has its own hard
instance, as printed ("can be obtained"); `p = ∞` is the `ℓ∞` norm `supNorm` with factor
`d^{−1}`. -/
theorem theorem_4_10 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d n n' : ℕ), 1 ≤ n → 1 ≤ n' →
      ∀ M : (N : ℕ) → PhaseEstimator N d (Vec d),
        (∀ N, (M N).numU ≤ n ∧ (M N).numPh ≤ n') →
        let f : ℝ :=
          if (n' : ℝ) < d then (d : ℝ)
          else if (n : ℝ) < d then max (d / Real.sqrt n) ((d : ℝ) ^ 2 / n')
          else max ((d : ℝ) ^ ((3 : ℝ) / 2) / n) ((d : ℝ) ^ 2 / n')
        (∃ (N : ℕ) (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d),
          IsPMF P ∧ (∀ ω j, |X ω j| ≤ 1 / 4) ∧
          ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, IsQuantumExperiment P U ∧
            2 / 3 ≤ (M N).successProb U X
              {est | c * f ≤ lpNorm 1 (est - mean P X)}) ∧
        (∀ p : ℝ, 1 < p →
          ∃ (N : ℕ) (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d),
            IsPMF P ∧ (∀ ω j, |X ω j| ≤ 1 / 4) ∧
            ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, IsQuantumExperiment P U ∧
              2 / 3 ≤ (M N).successProb U X
                {est | c * ((d : ℝ) ^ (1 / p - 1) * f) ≤ lpNorm p (est - mean P X)}) ∧
        (∃ (N : ℕ) (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d),
          IsPMF P ∧ (∀ ω j, |X ω j| ≤ 1 / 4) ∧
          ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, IsQuantumExperiment P U ∧
            2 / 3 ≤ (M N).successProb U X
              {est | c * (f / d) ≤ supNorm (est - mean P X)}) := by sorry

end QMultiMean.Supplement
