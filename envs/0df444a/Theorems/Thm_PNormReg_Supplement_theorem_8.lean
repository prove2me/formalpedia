-- Prove2me | Theorems.Thm_PNormReg_Supplement_theorem_8
-- name    : PNormReg.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:57:07.672418+00:00
-- url     : https://prove2.me/theorems/bda87af8-c427-40a1-adee-50f333a4a4be
-- title:
--   Theorem 8, p.12 — approximate $\ell_\infty$-regression in times $\widetilde O(nd^{\omega-1}+nd\epsilon^{-1})$ and $\widetilde O(nd^{\omega-1}+nd\epsilon^{-2/3}+d^2\epsilon^{-2})$
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ have full column rank, $b\in\mathbb R^n$ and $\epsilon,\delta\in(0,1)$. There are two algorithms that each find, with probability at least $1-\delta$, a $(1+\epsilon)$-approximate solution of $\min_x\|Ax-b\|_\infty$, with respective running times
--
--   $$\widetilde O(nd^{\omega-1}+nd\epsilon^{-1})\quad\text{(variance reduction)},\qquad\widetilde O(nd^{\omega-1}+nd\epsilon^{-2/3}+d^2\epsilon^{-2})\quad\text{(ball acceleration)}.$$
--
--   Precisely, with $L=\log(2+n+1/\epsilon+1/\delta)$, for every $\tau>0$ there are programs and constants $C>0$, $K\in\mathbb N$ such that the first halts on every coin sequence within $C(n^{1+\tau}d^{\omega-1}+nd\epsilon^{-1})L^K$ steps and the second within $C(n^{1+\tau}d^{\omega-1}+nd\epsilon^{-2/3}+d^2\epsilon^{-2})L^K$ steps, and each, with probability at least $1-\delta$, returns $\hat x$ with $\|A\hat x-b\|_\infty\le(1+\epsilon)\|Ax-b\|_\infty$ for all $x$.
--
--   These improve the $\epsilon$-dependence of Theorem 7 at $p=\infty$; neither bound dominates the other.
--
--   **Formalization Note** Input: dense layout, real memory $\epsilon,\delta$, then $A$ row by row, then $b$.
--
--   Differences from the source:
--   - reading: "there is an algorithm" (no machine named) → one finite admissible program of PNormReg.Machine per runtime (two clauses); reason: the paper fixes no machine; same reading as the published goal Theorem 2
--   - reading: Õ(·) (footnote 2: n^{o(1)} from fast matrix multiplication and polylog factors in n, d, 1/ϵ, 1/δ) → for every τ > 0 one program with constants C, K: n^τ on the fast-matrix-multiplication term only, (log(2 + n + 1/ϵ + 1/δ))^K on the whole bound; reason: footnote 2 pins the hidden factors; same reading as Theorem 2
--   - encoding: input of problem (1) → dense layout: n, d; ϵ, δ, A row-major, b; reason: the paper names no input format
--   - encoding: with probability at least 1 − δ; f⋆_p = min_x f_p(x) → a measurable set of fair-coin tapes of probability ≥ 1 − δ on which the halted output satisfies the bound against every x; reason: the minimum exists, so "for every x" is the same condition; same as Theorem 2
--   - encoding: A ∈ ℝ^{n×d} (d ≥ 1 implicit) → 1 ≤ d; reason: excludes only the empty problem, where a zero time bound would forbid halting
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 8, p.12 (PDF p.13); problem (1) and footnotes 1–2, p.1

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PNormReg_Supplement_Layouts

open Matrix

namespace PNormReg

namespace Supplement

/-- **Theorem 8** (Approximate `ℓ∞`-regression), both runtimes.

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…), Theorem 8, p.12 (PDF p.13); problem (1) and footnotes 1–2, p.1.

"For p = ∞ and ϵ, δ ∈ (0, 1), there are algorithms that each find a (1+ϵ)-approximate solution to (1) with
probability at least 1−δ, with respective runtimes Õ(nd^{ω−1} + ndϵ^{−1}) (variance reduction),
Õ(nd^{ω−1} + ndϵ^{−2/3} + d^2ϵ^{−2}) (ball acceleration)."

Two clauses, one program each. For every `τ > 0` there are an admissible program and `C > 0`, `K ∈ ℕ`
such that for all `n`, `d ≥ 1`, full column rank `A`, `b`, `ϵ, δ ∈ (0, 1)`, every coin tape halts with
1. `work ≤ C·(n^{1+τ}d^{ω−1} + ndϵ^{−1})·(log(2 + n + 1/ϵ + 1/δ))^K` (variance reduction), resp.
2. `work ≤ C·(n^{1+τ}d^{ω−1} + ndϵ^{−2/3} + d²ϵ^{−2})·(log(2 + n + 1/ϵ + 1/δ))^K` (ball acceleration),

and with probability at least `1 − δ` the output `x̂` has `∥Ax̂ − b∥_∞ ≤ (1 + ϵ)∥Ax − b∥_∞` for all `x`.

**Formalization Note.**
* `n^τ` (footnote 2's `n^{o(1)}` from fast matrix multiplication) multiplies only `nd^{ω−1}`; the log
  power is footnote 2's polylogarithmic factor on the whole bound.
* Input: `denseInput [ϵ, δ] A b`. Machine, coin tape, `∀ τ` first, success event and `∀ x` for `f⋆` as
  in `PNormReg.theorem_2`. -/
theorem theorem_8 :
    (∀ τ : ℝ, 0 < τ →
      ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d : ℕ), 1 ≤ d → ∀ (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
          Function.Injective A.mulVec →
          ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P (denseInput [ε, δ] A b) ω t).halted = true ∧
              ((run P (denseInput [ε, δ] A b) ω t).work : ℝ) ≤
                C * ((n : ℝ) ^ (1 + τ) *
                      (d : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ - 1) +
                    n * d * ε ^ (-1 : ℝ)) *
                  Real.log (2 + n + 1 / ε + 1 / δ) ^ K) ∧
            ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - δ ≤ (coinTape E).toReal ∧
              ∀ ω ∈ E, ∀ t : ℕ, (run P (denseInput [ε, δ] A b) ω t).halted = true →
                ∀ x : Fin d → ℝ,
                  linfNorm (A *ᵥ outputVec d (run P (denseInput [ε, δ] A b) ω t) - b) ≤
                    (1 + ε) * linfNorm (A *ᵥ x - b)) ∧
    (∀ τ : ℝ, 0 < τ →
      ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d : ℕ), 1 ≤ d → ∀ (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
          Function.Injective A.mulVec →
          ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P (denseInput [ε, δ] A b) ω t).halted = true ∧
              ((run P (denseInput [ε, δ] A b) ω t).work : ℝ) ≤
                C * ((n : ℝ) ^ (1 + τ) *
                      (d : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ - 1) +
                    n * d * ε ^ (-(2 / 3) : ℝ) + (d : ℝ) ^ 2 * ε ^ (-2 : ℝ)) *
                  Real.log (2 + n + 1 / ε + 1 / δ) ^ K) ∧
            ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - δ ≤ (coinTape E).toReal ∧
              ∀ ω ∈ E, ∀ t : ℕ, (run P (denseInput [ε, δ] A b) ω t).halted = true →
                ∀ x : Fin d → ℝ,
                  linfNorm (A *ᵥ outputVec d (run P (denseInput [ε, δ] A b) ω t) - b) ≤
                    (1 + ε) * linfNorm (A *ᵥ x - b)) := by sorry

end Supplement

end PNormReg
