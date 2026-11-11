-- Prove2me | Theorems.Thm_QMultiMean_theorem_3_5_euclidean_estimator
-- name    : QMultiMean.theorem_3_5_euclidean_estimator
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:13:33.858429+00:00
-- url     : https://prove2.me/theorems/57f2ab0b-eb80-45dc-b62e-9ab1b51fa2f3
-- title:
--   Theorem 3.5 — multivariate estimator in Euclidean norm with $\tilde O(n)$ queries (corrected: $\max\{1,n\}$)
-- statement:
--   Let $d\ge1$, $\delta\in(0,1)$ and let $n\ge\log(d/\delta)$ be real. There is a quantum estimator, chosen from $d,n,\delta$, $\Omega$ and $E$ only, with the following property. For every finite random variable $X:\Omega\to E\subset\mathbb R^d$ with mean $\mu$ and covariance matrix $\Sigma$, and every quantum experiment and binary oracle of $X$, it outputs $\tilde\mu$ with
--   $$\|\tilde\mu-\mu\|_2\le\begin{cases}\sqrt{\dfrac{\mathrm{Tr}(\Sigma)}n}+\sqrt{\dfrac{\|\Sigma\|\log(1/\delta)}n}, & n\le d,\\[2ex] \dfrac{\sqrt{d\,\mathrm{Tr}(\Sigma)}\,\log(d/\delta)}n, & n>d,\end{cases}$$
--   with probability at least $1-\delta$. It uses at most
--   $$C\max\{1,n\}\,\big(1+\log(1+n)+\log d\big)^k$$
--   quantum experiments and binary oracle queries, where $C$ and $k$ are universal constants.
--
--   Classically, $n$ samples give the first error bound and no better (Lugosi–Mendelson). The second bound is smaller than the first when $n>d$, up to the logarithmic factor, and the paper's Theorems 3.7–3.8 show both regimes are optimal up to logarithmic factors.
--
--   Differences from the source:
--   - reading: an informal quantum estimator / algorithm using quantum experiments and binary oracle queries → an oracle circuit (unitary gates, calls to U_P, U_P⁻¹, B_X, B_X⁻¹ on copies of H_Ω⊗H_E, final computational-basis measurement, classical output map) chosen from the parameters, Ω and E before P, X and the oracles, and successful for every pair of unitaries meeting Definitions 2.5–2.6; reason: the paper defines no model of computation; this is the standard query model its proofs use, and the oracles are specified only on |0⟩ and |ω⟩|0⃗⟩
--   - correction: Õ(n) quantum experiments and binary oracle queries → at most C·max(1, n)·(1 + log(1+n) + log d)^k calls; reason: the literal bound tends to 0 (as n → 0, since n ≥ log(d/δ) may be below 1 when d = 1) and then allows 0 queries; counterexample: on Ω = {0} take E containing 0 and K > 1/(1−δ) distinct constants c₁, …, c_K and X ≡ c_i; the error target is then the exact value c_i, a 0-query estimator has one output law for all i, so it cannot output each c_i with probability ≥ 1 − δ
--   - reading: Õ(n): polylogarithmic factors in the argument n → C·max(1,n)·(1 + log(1+n) + log d)^k with universal C, k chosen before every other quantity; reason: the paper's own count O(n/α) with α = 1/√log(400πn√d) (p.11) is polylogarithmic in n and d, uniformly in δ; the explicit form is required for a non-asymptotic statement
--   - generalization: E ⊂ ℝ^d the finite support of X, with 0⃗ ∈ E assumed (Definitions 2.2, 2.6) → E any finite set containing 0 and every value X(ω); reason: the support together with 0 is one admissible E, so the statement specializes to the source's
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the natural log gives the weaker hypothesis n ≥ log(d/δ) and the smaller error bound, so it is the stronger reading; a base change is absorbed by the query constant
--   - encoding: d ∈ ℕ the dimension → 1 ≤ d; reason: log(d/δ) is undefined at d = 0
--   - encoding: Tr(Σ) and the spectral norm ‖Σ‖ of Σ = E[XXᵀ] − E[X]E[X]ᵀ → traceCov = Σ_ω P(ω)‖X(ω) − µ‖₂² and covNorm = sup over unit v of Σ_ω P(ω)⟨v, X(ω) − µ⟩²; reason: equal for a probability mass function (Σ is positive semidefinite)
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.13, Theorem 3.5

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_OracleCircuit

set_option autoImplicit false

namespace QMultiMean

/-- Theorem 3.5 (Multivariate estimator in Euclidean norm) of Cornelissen, Hamoudi, Jerbi,
*Near-Optimal Quantum Algorithms for Multivariate Mean Estimation*, arXiv:2111.09787v2, p.13: there
exists a quantum estimator such that, for every `d`-dimensional random variable `X` with mean `µ` and
covariance matrix `Σ` and all reals `δ ∈ (0, 1)` and `n ≥ log(d/δ)`, it outputs `µ̃` with
`‖µ̃ − µ‖₂ ≤ √(Tr(Σ)/n) + √(‖Σ‖ log(1/δ)/n)` if `n ≤ d`, and
`‖µ̃ − µ‖₂ ≤ √(d Tr(Σ)) log(d/δ)/n` if `n > d`, with probability at least `1 − δ`, using `Õ(n)`
quantum experiments and binary oracle queries to `X`.

**Formalization Note.** A quantum estimator is an oracle circuit followed by a computational-basis
measurement and a classical output map (`Estimator`), built from `d, n, δ`, the sample set
`Ω = Fin (N+1)` and the value set `E` before the instance (`P`, `X`) and the oracles; success is
required for every pair of unitaries meeting Definitions 2.5–2.6. `Õ(n)` is
`C·max(1, n)·(1 + log(1+n) + log d)^k` with universal `C, k` chosen first (natural log); the
`max(1, ·)` corrects the literal bound, which tends to `0` as `n → 0`. `Tr(Σ)` is
`Σ_ω P(ω)‖X(ω) − µ‖₂²` and `‖Σ‖` the largest directional variance (the spectral norm). `d ≥ 1`. `E`
is any finite set containing `0` and the values of `X`. -/
theorem theorem_3_5_euclidean_estimator :
    ∃ C : ℝ, ∃ k : ℕ, ∀ (d : ℕ), 1 ≤ d → ∀ (δ n : ℝ), 0 < δ → δ < 1 → Real.log (d / δ) ≤ n →
      ∀ (N : ℕ) (E : Finset (Vec d)) (h0 : (0 : Vec d) ∈ E),
      ∃ M : Estimator N E (Vec d),
        (M.T : ℝ) ≤ C * max 1 n * (1 + Real.log (1 + n) + Real.log d) ^ k ∧
        ∀ (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d), IsPMF P → (∀ ω, X ω ∈ E) →
          ∀ (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
            (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ),
            IsQuantumExperiment P U → IsBinaryOracle E h0 X B →
            1 - δ ≤ M.successProb h0 U B
              {est | ‖est - mean P X‖ ≤
                if n ≤ d then
                  Real.sqrt (traceCov P X / n) + Real.sqrt (covNorm P X * Real.log (1 / δ) / n)
                else
                  Real.sqrt (d * traceCov P X) * Real.log (d / δ) / n} := by sorry

end QMultiMean
