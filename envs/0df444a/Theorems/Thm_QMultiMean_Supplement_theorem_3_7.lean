-- Prove2me | Theorems.Thm_QMultiMean_Supplement_theorem_3_7
-- name    : QMultiMean.Supplement.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:14:18.914193+00:00
-- url     : https://prove2.me/theorems/cf382f8e-aea7-49c0-bfb8-a15b8572fb41
-- title:
--   Theorem 3.7 — low-precision regime: with $n\le d/\alpha$ binary oracle queries the Euclidean error is $\Omega(\sqrt{\mathrm{Tr}\Sigma/n})$
-- statement:
--   There is a constant $\alpha>1$ (the constant of Lemma 3.6) and a constant $c>0$ with the following property. Let $n,d$ be integers with $n\ge1$ and $n\le d/\alpha$, and let $\sigma>0$. Let $\mathcal P_\sigma$ be the set of $d$-dimensional finite random variables whose covariance matrix $\Sigma$ satisfies $\mathrm{Tr}(\Sigma)=\sigma^2$. Then for every quantum estimator that uses at most $n$ binary oracle queries there is $X\in\mathcal P_\sigma$ with mean $\mu=\mathbb E[X]$, together with a quantum experiment and a binary oracle for $X$, such that the estimate $\tilde\mu$ returned by the estimator satisfies
--   $$\|\tilde\mu-\mu\|_2\ \ge\ c\sqrt{\frac{\mathrm{Tr}(\Sigma)}{n}}$$
--   with probability at least $2/3$.
--
--   So when the number of queries is below the dimension, quantum estimators do no better than the classical sub-Gaussian rate $\sqrt{\mathrm{Tr}(\Sigma)/n}$: the first branch of Theorem 3.5 is optimal up to constants.
--
--   **Formalization Note** A quantum estimator is a family of published `Estimator` circuits, one per sample set $\Omega$ and value set $E\ni0$, fixed before the instance. Only binary oracle queries ($B_X$, $B_X^{-1}$) are counted; quantum experiments are free.
--
--   Differences from the source:
--   - reading: "any quantum estimator that uses at most n binary oracle queries" (no formal model in the paper) → a family of published QMultiMean.Estimator circuits, one per sample set Ω = Fin (N+1) and finite value set E ∋ 0, fixed before the instance, with at most n calls of kind B_X or B_X⁻¹ (quantum experiments not counted); reason: the base mission's published binary-oracle model; the estimator may not see X, and the theorem bounds only binary oracle queries
--   - reading: there exists X ∈ P_σ → there exist N, E, a PMF P, X with values in E and Tr(Σ) = σ², a quantum experiment U_P (Definition 2.5) and a binary oracle B_X (Definition 2.6); reason: Definitions 2.5–2.6 fix the oracles only on part of the space; the hard instance includes the oracle pair, and failure for every valid oracle would be false because B_X's other columns can leak X
--   - reading: ‖µ̃ − µ‖₂ ≥ Ω(√(Tr(Σ)/n)) with probability at least 2/3 → a constant c > 0 chosen before n, d, σ and the estimator, and probability at least 2/3 that ‖µ̃ − µ‖₂ ≥ c·√(Tr(Σ)/n); reason: standard reading of Ω; the same uniform-constant reading the published base items give Õ/O
--   - encoding: two integers n, d → natural numbers with n ≥ 1; reason: √(Tr(Σ)/n) is undefined at n = 0, and n counts queries
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.14, Theorem 3.7

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_OracleCircuit

set_option autoImplicit false

namespace QMultiMean.Supplement

open QMultiMean

/-- Theorem 3.7 (Low-precision regime) of Cornelissen, Hamoudi, Jerbi, *Near-Optimal Quantum
Algorithms for Multivariate Mean Estimation*, arXiv:2111.09787v2, p.14: there is a constant `α > 1`
(the constant of Lemma 3.6) such that, for integers `n, d` with `n ≤ d/α` and every `σ > 0`, every
quantum estimator that uses at most `n` binary oracle queries has, on some `d`-dimensional random
variable `X` with `Tr(Σ) = σ²`, an output `µ̃` with `‖µ̃ − µ‖₂ ≥ Ω(√(Tr(Σ)/n))` with probability at
least `2/3`.

**Formalization Note.** `Ω(·)` is a universal constant `c > 0` chosen, like `α`, before every other
parameter. A quantum estimator is a family of published `QMultiMean.Estimator`s, one for each sample
set `Ω = Fin (N+1)` and finite value set `E ∋ 0`, fixed before the instance; only binary oracle
queries (`B_X`, `B_X⁻¹`) are counted, quantum experiments are free. The adversary chooses `N`, `E`,
the probability mass function `P`, the random variable `X` (with values in `E`, `Tr(Σ) = σ²`), a
quantum experiment `U_P` (Definition 2.5) and a binary oracle `B_X` (Definition 2.6). `Tr(Σ)` is the
published `traceCov`; `n ≥ 1`. -/
theorem theorem_3_7 :
    ∃ α : ℝ, 1 < α ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ), 1 ≤ n → (n : ℝ) ≤ d / α → ∀ σ : ℝ, 0 < σ →
      ∀ M : (N : ℕ) → (E : Finset (Vec d)) → (0 : Vec d) ∈ E → Estimator N E (Vec d),
        (∀ N E h0, (Finset.univ.filter (fun t => (M N E h0).kind t = CallKind.B ∨
            (M N E h0).kind t = CallKind.Binv)).card ≤ n) →
        ∃ (N : ℕ) (E : Finset (Vec d)) (h0 : (0 : Vec d) ∈ E)
          (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d),
          IsPMF P ∧ (∀ ω, X ω ∈ E) ∧ traceCov P X = σ ^ 2 ∧
          ∃ (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
            (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ),
            IsQuantumExperiment P U ∧ IsBinaryOracle E h0 X B ∧
            2 / 3 ≤ (M N E h0).successProb h0 U B
              {est | c * Real.sqrt (traceCov P X / n) ≤ ‖est - mean P X‖} := by sorry

end QMultiMean.Supplement
