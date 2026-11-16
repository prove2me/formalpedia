-- Prove2me | Theorems.Thm_QMultiMean_Supplement_theorem_4_7
-- name    : QMultiMean.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:17:59.712194+00:00
-- url     : https://prove2.me/theorems/6b69ff2e-cc20-4b5b-8720-c51cde35482b
-- title:
--   Theorem 4.7 — with $n'\ge d$ phase oracle queries the $\ell_1$ error is $\Omega(d^2/n')$
-- statement:
--   There is a constant $c>0$ with the following property. Let $d\in\mathbb N$ and $n'\ge d$, and consider a quantum algorithm that approximates the mean $\mu$ of any random variable with values in $[-1/4,1/4]^d$ using at most $n'$ queries to the phase oracle $\mathcal P_X$ (calls to $U_{\mathbb P}$ are not limited). Then there is an instance (a distribution, a random variable $X$ with values in $[-1/4,1/4]^d$ and a quantum experiment $U_{\mathbb P}$) on which the output $\tilde\mu$ satisfies
--   $$\|\tilde\mu-\mu\|_1\ \ge\ c\,\frac{d^2}{n'}$$
--   with probability at least $2/3$.
--
--   This shows that the $d/n'$ term of Theorem 4.3 (which gives $\ell_1$ error $d^2/n'$) cannot be improved beyond logarithmic factors.
--
--   **Formalization Note** The algorithm is a family of phase-oracle estimators, one per sample set, fixed before the instance. The case $d=0$ is allowed and trivial.
--
--   Differences from the source:
--   - reading: "a quantum algorithm that finds an approximation µ̃ of the mean of any random variable with values in [−1/4,1/4]^d" (no formal model in the paper) → a family of PhaseEstimators, one per sample set Ω = Fin (N+1), fixed before the instance (uncontrolled U_P/U_P⁻¹, controlled P_X/P_X⁻¹); the adversary picks N, a PMF P, X with values in [−1/4,1/4]^d and a quantum experiment U_P meeting Definition 2.5 (P_X is determined by X); reason: the upper bounds' model; U_P is fixed by Definition 2.5 only on |0⟩, so the hard instance includes it
--   - reading: ‖µ̃ − µ‖₁ = Ω(d²/n′) with probability at least 2/3 → a universal constant c > 0 chosen first, and probability at least 2/3 that ‖µ̃ − µ‖₁ ≥ c·d²/n′; reason: standard reading of Ω, read literally as a lower bound holding with probability at least 2/3
--   - reading: using n′ queries to P_X → using at most that many, on every sample set; reason: fewer queries can always be padded with unused ones
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.25, Theorem 4.7

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_Supplement_phaseOracle
import Definitions.Def_QMultiMean_Supplement_PhaseCircuit
import Definitions.Def_QMultiMean_Supplement_lpNorm

set_option autoImplicit false

namespace QMultiMean.Supplement

open QMultiMean

/-- Theorem 4.7 of Cornelissen, Hamoudi, Jerbi, *Near-Optimal Quantum Algorithms for Multivariate
Mean Estimation*, arXiv:2111.09787v2, p.25: let `d ∈ ℕ`, `n′ ≥ d`, and consider a quantum algorithm
that approximates the mean `µ` of any random variable with values in `[−1/4, 1/4]^d` using `n′`
queries to `P_X`. Then there are instances on which its output `µ̃` satisfies
`‖µ̃ − µ‖₁ = Ω(d²/n′)` with probability at least `2/3`.

**Formalization Note.** `Ω(·)` is a universal constant `c > 0` chosen before every other
parameter. A quantum algorithm is a family of `PhaseEstimator`s, one for each sample set
`Ω = Fin (N+1)`, fixed before the instance (uncontrolled `U_P`/`U_P⁻¹` calls, controlled
`P_X`/`P_X⁻¹` calls, computational-basis measurement, classical output map). The adversary chooses
`N`, the probability mass function `P`, the random variable `X` with values in `[−1/4, 1/4]^d` (every
coordinate of every value) and a quantum experiment `U_P` meeting Definition 2.5; the phase oracle
`P_X` (Definition 2.7) is determined by `X`. "Error `Ω(f)` with probability at least `2/3`" is read
literally: the output satisfies `‖µ̃ − µ‖ ≥ c·f` with probability at least `2/3`. "Using `n` queries"
is "using at most `n` queries" on every sample set. `‖·‖₁` is `lpNorm 1`. `d = 0` is allowed (the
statement is then trivially true). Only queries to `P_X` are counted; calls to `U_P` are unlimited. -/
theorem theorem_4_7 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d n' : ℕ), d ≤ n' →
      ∀ M : (N : ℕ) → PhaseEstimator N d (Vec d), (∀ N, (M N).numPh ≤ n') →
        ∃ (N : ℕ) (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d),
          IsPMF P ∧ (∀ ω j, |X ω j| ≤ 1 / 4) ∧
          ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, IsQuantumExperiment P U ∧
            2 / 3 ≤ (M N).successProb U X
              {est | c * ((d : ℝ) ^ 2 / n') ≤ lpNorm 1 (est - mean P X)} := by sorry

end QMultiMean.Supplement
