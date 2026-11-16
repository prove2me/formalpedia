-- Prove2me | Theorems.Thm_PNormReg_Supplement_theorem_1
-- name    : PNormReg.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:53:30.482445+00:00
-- url     : https://prove2.me/theorems/f372d0fe-f063-4655-a62b-3dd9e2d117f4
-- title:
--   Theorem 1, p.2 — a $(1+\epsilon)$-approximate $\ell_\infty$-regression solution with probability $1-\delta$ in time $\widetilde O(nd^{\omega-1}\mathrm{poly}(\epsilon^{-1}))$
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ have full column rank, $b\in\mathbb R^n$ and $\epsilon,\delta\in(0,1)$. There is a randomized algorithm which, with probability at least $1-\delta$, returns $\hat x$ with
--
--   $$\|A\hat x-b\|_\infty\le(1+\epsilon)\min_{x\in\mathbb R^d}\|Ax-b\|_\infty,$$
--
--   in time $\widetilde O(nd^{\omega-1}\mathrm{poly}(\epsilon^{-1}))$, where $\omega$ is the matrix multiplication exponent. Precisely: for every $\tau>0$ there are one program and constants $C>0$, $K\in\mathbb N$ such that on every input and every coin sequence the program halts within
--
--   $$C\,n^{1+\tau}d^{\omega-1}\epsilon^{-K}\big(\log(2+n+1/\epsilon+1/\delta)\big)^K$$
--
--   steps.
--
--   This is the paper's headline low-accuracy result for $\ell_\infty$-regression; no dependence on the condition number of $A$ appears.
--
--   **Formalization Note** The machine and the probability model are the base mission's (as in Theorem 2). Input: integer memory $n,d$; real memory $\epsilon,\delta$, then $A$ row by row, then $b$.
--
--   Differences from the source:
--   - reading: "there is an algorithm" (no machine named) → one finite admissible program of the base mission's randomized exact-arithmetic real RAM (PNormReg.Machine), time = executed instructions on every coin tape; reason: the paper fixes no machine; same reading as the published goal Theorem 2
--   - reading: Õ(·) (footnote 2: n^{o(1)} from fast matrix multiplication and polylog factors in n, d, 1/ϵ, 1/δ) → for every τ > 0 one program with constants C, K: n^τ on the fast-matrix-multiplication term only, (log(2 + n + 1/ϵ + 1/δ))^K on the whole bound; reason: footnote 2 pins the hidden factors; same reading as Theorem 2
--   - reading: poly(ϵ^{−1}) → (1/ϵ)^K with K chosen with the program; reason: a polynomial in 1/ϵ ≥ 1 is bounded by a constant times a power of 1/ϵ
--   - encoding: input of problem (1) → dense layout: n, d; ϵ, δ, A row-major, b; reason: the paper names no input format
--   - encoding: with probability at least 1 − δ; f⋆_p = min_x f_p(x) → a measurable set of fair-coin tapes of probability ≥ 1 − δ on which the halted output satisfies the bound against every x; reason: the minimum exists, so "for every x" is the same condition; same as Theorem 2
--   - encoding: A ∈ ℝ^{n×d} (d ≥ 1 implicit) → 1 ≤ d; reason: excludes only the empty problem, where a zero time bound would forbid halting
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 1, p.2 (PDF p.3); problem (1) and footnotes 1–2, p.1

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PNormReg_Supplement_Layouts

open Matrix

namespace PNormReg

namespace Supplement

/-- **Theorem 1** (Approximate `ℓ∞`-regression).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…), Theorem 1, p.2 (PDF p.3); problem (1) and footnotes 1–2, p.1.

"For p = ∞ and ϵ, δ ∈ (0, 1), there is an algorithm which returns a (1+ϵ)-approximate solution to (1),
with probability at least 1−δ, in time Õ(nd^{ω−1}poly(ϵ^{−1}))."

For every `τ > 0` there are one admissible program `P` and constants `C > 0`, `K ∈ ℕ` such that for all
`n`, `d ≥ 1`, full column rank `A`, `b` and `ϵ, δ ∈ (0, 1)`, with
`T = C·n^{1+τ}·d^{ω−1}·(1/ϵ)^K·(log(2 + n + 1/ϵ + 1/δ))^K`: every coin tape halts with `work ≤ T`, and a
measurable set of tapes of probability at least `1 − δ` gives a halted output `x̂` with
`∥Ax̂ − b∥_∞ ≤ (1 + ϵ)∥Ax − b∥_∞` for all `x`.

**Formalization Note.**
* Machine, coin tape, `∀ τ` first, the success event and `∀ x` for `f⋆` are as in `PNormReg.theorem_2`.
* `poly(ϵ^{−1})` is read as `(1/ϵ)^K` with `K` chosen with the program; the `n^τ` is footnote 2's
  `n^{o(1)}`, the log power footnote 2's polylogarithmic factor.
* Input: `denseInput [ϵ, δ] A b` (integer memory `n, d`; real memory `ϵ, δ`, `A` row-major, `b`).
* `d ≥ 1`: at `d = 0`, `d^{ω−1} = 0` would forbid halting. -/
theorem theorem_1 :
    ∀ τ : ℝ, 0 < τ →
      ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d : ℕ), 1 ≤ d → ∀ (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
          Function.Injective A.mulVec →
          ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P (denseInput [ε, δ] A b) ω t).halted = true ∧
              ((run P (denseInput [ε, δ] A b) ω t).work : ℝ) ≤
                C * (n : ℝ) ^ (1 + τ) *
                  (d : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ - 1) *
                  (1 / ε) ^ K * Real.log (2 + n + 1 / ε + 1 / δ) ^ K) ∧
            ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - δ ≤ (coinTape E).toReal ∧
              ∀ ω ∈ E, ∀ t : ℕ, (run P (denseInput [ε, δ] A b) ω t).halted = true →
                ∀ x : Fin d → ℝ,
                  linfNorm (A *ᵥ outputVec d (run P (denseInput [ε, δ] A b) ω t) - b) ≤
                    (1 + ε) * linfNorm (A *ᵥ x - b) := by sorry

end Supplement

end PNormReg
