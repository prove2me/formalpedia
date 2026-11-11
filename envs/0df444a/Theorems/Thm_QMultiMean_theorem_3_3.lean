-- Prove2me | Theorems.Thm_QMultiMean_theorem_3_3
-- name    : QMultiMean.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:38.023058+00:00
-- url     : https://prove2.me/theorems/7c04cc4f-83eb-466e-bcc7-1edac29bc023
-- title:
--   Theorem 3.3 — bounded multivariate estimator: $\|\tilde\mu-\mu\|_\infty\le\sqrt{L_2}\log(d/\delta)/n$ with $\tilde O(n)$ queries
-- statement:
--   Let $d\ge1$ and let $X$ be a finite random variable over $\mathbb R^d$ with $\|X\|_2\le1$ and mean $\mu$. Let $L_2\in(0,1]$, $\delta\in(0,1)$ and $n\ge1$ be reals with $\mathbb E[\|X\|_2]\le L_2$. There is a quantum estimator, chosen from $d,L_2,n,\delta$, $\Omega$ and $E$ only, that outputs $\tilde\mu$ with
--   $$\|\tilde\mu-\mu\|_\infty\le\frac{\sqrt{L_2}\,\log(d/\delta)}{n}$$
--   with probability at least $1-\delta$, for every quantum experiment and binary oracle of $X$. It uses at most $C\max\{1,n\}(1+\log(1+n)+\log d)^k$ quantum experiments and binary oracle queries, where $C,k$ are universal constants.
--
--   This is the bounded estimator (Algorithm 1) that Algorithm 2 applies to each rescaled slice of $X$.
--
--   Differences from the source:
--   - reading: an informal quantum estimator / algorithm using quantum experiments and binary oracle queries → an oracle circuit (unitary gates, calls to U_P, U_P⁻¹, B_X, B_X⁻¹ on copies of H_Ω⊗H_E, final computational-basis measurement, classical output map) chosen from the parameters, Ω and E before P, X and the oracles, and successful for every pair of unitaries meeting Definitions 2.5–2.6; reason: the paper defines no model of computation; this is the standard query model its proofs use, and the oracles are specified only on |0⟩ and |ω⟩|0⃗⟩
--   - reading: the bounded multivariate estimator QBounded_d(X, L₂, n, δ) (Algorithm 1) → there exists an estimator with the stated guarantee; reason: Algorithm 1 is given modulo cited subroutines (Proposition 3.2 via [Low17], [GL20], [GAW19]), so no concrete circuit is fixed by the paper
--   - reading: Õ(n): polylogarithmic factors in the argument n → C·max(1,n)·(1 + log(1+n) + log d)^k with universal C, k chosen before every other quantity; reason: the paper's own count O(n/α) with α = 1/√log(400πn√d) (p.11) is polylogarithmic in n and d, uniformly in δ; the explicit form is required for a non-asymptotic statement
--   - generalization: E ⊂ ℝ^d the finite support of X, with 0⃗ ∈ E assumed (Definitions 2.2, 2.6) → E any finite set containing 0 and every value X(ω); reason: the support together with 0 is one admissible E, so the statement specializes to the source's
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the natural log gives the weaker hypothesis n ≥ log(d/δ) and the smaller error bound, so it is the stronger reading; a base change is absorbed by the query constant
--   - encoding: d ∈ ℕ the dimension → 1 ≤ d; reason: log(d/δ) is undefined at d = 0
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, pp.10–11, Theorem 3.3

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_IsBinaryOracle
import Definitions.Def_QMultiMean_OracleCircuit

set_option autoImplicit false

namespace QMultiMean

/-- Theorem 3.3 (Bounded multivariate estimator) of Cornelissen, Hamoudi, Jerbi,
arXiv:2111.09787v2, p.10: let `X` be a `d`-dimensional random variable with `‖X‖₂ ≤ 1`. Given reals
`L₂ ∈ (0, 1]`, `δ ∈ (0, 1)` and `n ≥ 1` such that `E[‖X‖₂] ≤ L₂`, the bounded multivariate estimator
`QBounded_d(X, L₂, n, δ)` (Algorithm 1) outputs `µ̃` with `‖µ̃ − µ‖∞ ≤ √L₂ log(d/δ)/n` with
probability at least `1 − δ`, using `Õ(n)` quantum experiments and binary oracle queries.

**Formalization Note.** Algorithm 1 calls cited subroutines, so the theorem is stated as the
existence of an estimator with its guarantee, built from `d, L₂, n, δ, N, E` before the instance
(`P`, `X`) and the oracles, and successful for every pair of oracles meeting Definitions 2.5–2.6.
`Õ(n)` is `C·max(1, n)·(1 + log(1+n) + log d)^k` with universal `C, k` chosen first (natural log;
polylogarithmic in `n` and `d`, uniformly in `L₂` and `δ`). `d ≥ 1` so that `log(d/δ)` is defined.
`E` is any finite set containing `0` and the values of `X`. -/
theorem theorem_3_3 :
    ∃ C : ℝ, ∃ k : ℕ, ∀ (d : ℕ), 1 ≤ d → ∀ (L₂ δ n : ℝ), 0 < L₂ → L₂ ≤ 1 → 0 < δ → δ < 1 →
      1 ≤ n →
      ∀ (N : ℕ) (E : Finset (Vec d)) (h0 : (0 : Vec d) ∈ E),
      ∃ M : Estimator N E (Vec d),
        (M.T : ℝ) ≤ C * max 1 n * (1 + Real.log (1 + n) + Real.log d) ^ k ∧
        ∀ (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d), IsPMF P → (∀ ω, X ω ∈ E) →
          (∀ ω, ‖X ω‖ ≤ 1) → expect P (fun ω => ‖X ω‖) ≤ L₂ →
          ∀ (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
            (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ),
            IsQuantumExperiment P U → IsBinaryOracle E h0 X B →
            1 - δ ≤ M.successProb h0 U B
              {est | supNorm (est - mean P X) ≤ Real.sqrt L₂ * Real.log (d / δ) / n} := by sorry

end QMultiMean
