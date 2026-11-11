-- Prove2me | Theorems.Thm_QMultiMean_random_experiment_simulation
-- name    : QMultiMean.random_experiment_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:31.106747+00:00
-- url     : https://prove2.me/theorems/4a56575e-fa9c-4dd0-8c8f-046f3ee0a226
-- title:
--   p.7 — a random experiment is simulated by one quantum experiment and one binary oracle query
-- statement:
--   Let $K\ge0$ and let $f$ be any map from $K$-tuples of values to outputs. There is a quantum estimator with exactly $2K$ oracle calls (for each $i<K$: $U_P$, then $\mathcal B_X$, on the $i$-th copy of $\mathcal H_\Omega\otimes\mathcal H_E$) such that, for every finite random variable $X:\Omega\to E$, every quantum experiment $U_P$ and every binary oracle $\mathcal B_X$, and every set $S$ of outputs,
--   $$\Pr[\text{the estimator outputs a point of }S]=\Pr_{\omega_1,\dots,\omega_K\sim P\text{ i.i.d.}}\big[f(X(\omega_1),\dots,X(\omega_K))\in S\big].$$
--
--   This is how the classical estimator of Proposition 2.8 runs inside the quantum model, in the $n\le d$ regime of Theorem 3.5 and in step 2 of Algorithm 2.
--
--   Differences from the source:
--   - generalization: one random experiment is simulated using one quantum experiment and one call to the binary oracle → K random experiments followed by any classical post-processing f are simulated with exactly 2K calls; reason: K = 1 with f the identity is the source's statement
--   - reading: can be simulated by preparing Σ_ω √P(ω)|ω⟩|X(ω)⟩ and measuring its last register → an estimator chosen from K, f, N, E whose output law equals the law of f(X(ω₁), …, X(ω_K)) for every instance and every valid oracle pair; reason: equality of output laws is what simulation means
--   - generalization: E ⊂ ℝ^d the finite support of X, with 0⃗ ∈ E assumed (Definitions 2.2, 2.6) → E any finite set containing 0 and every value X(ω); reason: the support together with 0 is one admissible E, so the statement specializes to the source's
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.7, paragraph after Definition 2.6

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_OracleCircuit

set_option autoImplicit false

namespace QMultiMean

/-- The observation after Definition 2.6 of Cornelissen, Hamoudi, Jerbi, arXiv:2111.09787v2, p.7:
one random experiment can be simulated by preparing `Σ_ω √P(ω)|ω⟩|X(ω)⟩` and measuring its last
register, using one quantum experiment and one call to the binary oracle. Stated for `K` random
experiments followed by any classical post-processing `f`: there is an estimator with exactly `2K`
oracle calls whose output law equals the law of `f(X(ω₁), …, X(ω_K))` for i.i.d. `ω_i ∼ P`, for
every instance and every pair of oracles meeting Definitions 2.5–2.6.

**Formalization Note.** "Can be simulated" is read as equality of output laws: for every set `S`,
the probability of an output in `S` is the same. The estimator is chosen from `K, f, N, E` only. -/
theorem random_experiment_simulation {V Out : Type} [Zero V] (K : ℕ) (f : (Fin K → V) → Out)
    (N : ℕ) (E : Finset V) (h0 : (0 : V) ∈ E) :
    ∃ M : Estimator N E Out, M.T = 2 * K ∧
      ∀ (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → V), IsPMF P → (∀ ω, X ω ∈ E) →
        ∀ (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
          (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ),
          IsQuantumExperiment P U → IsBinaryOracle E h0 X B →
          ∀ S : Set Out, M.successProb h0 U B S = sampleProb P X K f S := by sorry

end QMultiMean
