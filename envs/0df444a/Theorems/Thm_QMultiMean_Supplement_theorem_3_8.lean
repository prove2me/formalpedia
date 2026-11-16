-- Prove2me | Theorems.Thm_QMultiMean_Supplement_theorem_3_8
-- name    : QMultiMean.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:15:17.492207+00:00
-- url     : https://prove2.me/theorems/3c6fe251-d6ce-45eb-8988-fd20c78749b4
-- title:
--   Theorem 3.8 — high-precision regime: with $n>d/\alpha$ binary oracle queries the Euclidean error is $\Omega(\sqrt{d\,\mathrm{Tr}\Sigma}/n)$
-- statement:
--   For every $\alpha>1$ there is a constant $c>0$ with the following property. Let $n,d$ be integers with $d\ge1$ and $n>d/\alpha$, and let $\sigma>0$. Let $\mathcal P_\sigma$ be the set of $d$-dimensional finite random variables whose covariance matrix $\Sigma$ satisfies $\mathrm{Tr}(\Sigma)=\sigma^2$. Then for every quantum estimator that uses at most $n$ binary oracle queries there is $X\in\mathcal P_\sigma$ with mean $\mu=\mathbb E[X]$, together with a quantum experiment and a binary oracle for $X$, such that the estimate $\tilde\mu$ returned by the estimator satisfies
--   $$\|\tilde\mu-\mu\|_2\ \ge\ c\,\frac{\sqrt{d\,\mathrm{Tr}(\Sigma)}}{n}$$
--   with probability at least $2/3$.
--
--   This shows that the second branch $\sqrt{d\,\mathrm{Tr}(\Sigma)}\log(d/\delta)/n$ of Theorem 3.5 is optimal up to logarithmic factors.
--
--   **Formalization Note** In the paper $\alpha$ is the constant of Lemma 3.6, shared with Theorem 3.7; the statement is made for every $\alpha>1$. The estimator model, the count of binary oracle queries only, and the hard instance are as in Theorem 3.7.
--
--   Differences from the source:
--   - generalization: n > d/α for the fixed constant α of Lemma 3.6 (shared with Theorem 3.7) → every α > 1, with c > 0 depending on α only; reason: specializes to the paper's α; for larger α the extra range d/α < n ≤ d/α₀ is covered by Theorem 3.7, since there √(Tr(Σ)/n) ≥ √(d·Tr(Σ))/(√α·n); stating ∃ α separately would decouple the two theorems' α
--   - reading: "any quantum estimator that uses at most n binary oracle queries" (no formal model in the paper) → a family of published QMultiMean.Estimator circuits, one per sample set Ω = Fin (N+1) and finite value set E ∋ 0, fixed before the instance, with at most n calls of kind B_X or B_X⁻¹ (quantum experiments not counted); reason: the base mission's published binary-oracle model; the estimator may not see X, and the theorem bounds only binary oracle queries
--   - reading: there exists X ∈ P_σ → there exist N, E, a PMF P, X with values in E and Tr(Σ) = σ², a quantum experiment U_P (Definition 2.5) and a binary oracle B_X (Definition 2.6); reason: Definitions 2.5–2.6 fix the oracles only on part of the space; the hard instance includes the oracle pair, and failure for every valid oracle would be false because B_X's other columns can leak X
--   - reading: ‖µ̃ − µ‖₂ ≥ Ω(√(d·Tr(Σ))/n) with probability at least 2/3 → a constant c > 0 chosen before n, d, σ and the estimator, and probability at least 2/3 that ‖µ̃ − µ‖₂ ≥ c·√(d·Tr(Σ))/n; reason: standard reading of Ω; the same uniform-constant reading the published base items give Õ/O
--   - encoding: two integers n, d → natural numbers with d ≥ 1; reason: for d = 0 the set P_σ is empty (Tr(Σ) = 0 ≠ σ²), so the source's statement concerns d ≥ 1; n ≥ 1 follows from n > d/α
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.14, Theorem 3.8

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_OracleCircuit

set_option autoImplicit false

namespace QMultiMean.Supplement

open QMultiMean

/-- Theorem 3.8 (High-precision regime) of Cornelissen, Hamoudi, Jerbi, *Near-Optimal Quantum
Algorithms for Multivariate Mean Estimation*, arXiv:2111.09787v2, p.14: for integers `n, d` with
`n > d/α` and every `σ > 0`, every quantum estimator that uses at most `n` binary oracle queries has,
on some `d`-dimensional random variable `X` with `Tr(Σ) = σ²`, an output `µ̃` with
`‖µ̃ − µ‖₂ ≥ Ω(√(d Tr(Σ))/n)` with probability at least `2/3`.

**Formalization Note.** The paper's `α` is the constant of Lemma 3.6 shared with Theorem 3.7; here the
statement is made for **every** `α > 1` (with `c > 0` depending on `α` only), which contains the
paper's case and, together with Theorem 3.7, is implied by the paper's pair. `Ω(·)` is a constant
`c > 0` chosen before `n, d, σ` and the estimator. The estimator model, the count of binary oracle
queries only, and the adversary's choices (`N`, `E`, `P`, `X`, `U_P`, `B_X`) are as in
`theorem_3_7`. `d ≥ 1` (for `d = 0` no random variable has `Tr(Σ) = σ² > 0`). -/
theorem theorem_3_8 :
    ∀ α : ℝ, 1 < α → ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ), 1 ≤ d → (d : ℝ) / α < n → ∀ σ : ℝ, 0 < σ →
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
              {est | c * Real.sqrt (d * traceCov P X) / n ≤ ‖est - mean P X‖} := by sorry

end QMultiMean.Supplement
