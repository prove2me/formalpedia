-- Prove2me | Theorems.Thm_PNormReg_Supplement_theorem_3
-- name    : PNormReg.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:53:56.783672+00:00
-- url     : https://prove2.me/theorems/e78d80ca-33b3-4eed-a0cc-f3bfd1548c4a
-- title:
--   Theorem 3, p.2 — a $(1+\epsilon)$-approximate $\ell_p$-regression solution for every $p\in(1,2]$, with probability $1-\delta$, in time $\widetilde O_p(\mathrm{nnz}(A)+d^\omega)$
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ have full column rank, $b\in\mathbb R^n$, $p\in(1,2]$ and $\epsilon,\delta\in(0,1)$. There is a randomized algorithm which, with probability at least $1-\delta$, returns $\hat x$ with
--
--   $$\|A\hat x-b\|_p\le(1+\epsilon)\min_{x\in\mathbb R^d}\|Ax-b\|_p,$$
--
--   in time $\widetilde O_p(\mathrm{nnz}(A)+d^\omega)$, where $\mathrm{nnz}(A)$ is the number of nonzero entries of $A$ plus $n+d$. Precisely: for every $\tau>0$ there are one program (serving every $p\in(1,2]$) and constants $C>0$, $K\in\mathbb N$ such that on every input and every coin sequence it halts within
--
--   $$C\Big(\frac{2}{p-1}\Big)^{K/(p-1)}\big(\mathrm{nnz}(A)+n^\tau d^{\omega}\big)\big(\log(2+n+1/\epsilon+1/\delta)\big)^K$$
--
--   steps.
--
--   This is the high-accuracy, input-sparsity-time result for $p$ below $2$, with only logarithmic dependence on $1/\epsilon$.
--
--   **Formalization Note** The $p$-dependent factor follows footnote 2 and p.27 ("exponential in $1/(p-1)$", $\log\Lambda_p=O((p-1)^{-1}\log(2/(p-1)))$). The matrix is read in the sparse layout (its nonzero entries with their positions), then $b$; the header holds $p,\epsilon,\delta$.
--
--   Differences from the source:
--   - reading: "there is an algorithm" (no machine named) → one finite admissible program of the base mission's randomized exact-arithmetic real RAM (PNormReg.Machine), time = executed instructions on every coin tape; reason: the paper fixes no machine; same reading as the published goal Theorem 2
--   - reading: Õ(·) (footnote 2: n^{o(1)} from fast matrix multiplication and polylog factors in n, d, 1/ϵ, 1/δ) → for every τ > 0 one program with constants C, K: n^τ on the fast-matrix-multiplication term only, (log(2 + n + 1/ϵ + 1/δ))^K on the whole bound; reason: footnote 2 pins the hidden factors; same reading as Theorem 2
--   - reading: Õ_p (footnote 2: factors exponential in 1/(p−1) for Theorem 3; p.27: log Λ_p = O((p−1)^{−1} log(2/(p−1)))) → factor (2/(p−1))^{K/(p−1)}, one K for all p ∈ (1, 2]; reason: this is the precise bound p.27 gives for Λ_p and covers every polynomial in 1/(p−1)
--   - encoding: input of problem (1) → sparse layout: nonzero entries of A with positions, then b; header p, ϵ, δ; reason: a dense matrix cannot be read in nnz(A) time; the paper names no format
--   - encoding: with probability at least 1 − δ; f⋆_p = min_x f_p(x) → a measurable set of fair-coin tapes of probability ≥ 1 − δ on which the halted output satisfies the bound against every x; reason: the minimum exists, so "for every x" is the same condition; same as Theorem 2
--   - encoding: A ∈ ℝ^{n×d} (d ≥ 1 implicit) → 1 ≤ d; reason: excludes only the empty problem, where a zero time bound would forbid halting
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 3, p.2 (PDF p.3); problem (1) and footnotes 1–2, p.1; Λ_p, p.27

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PNormReg_Supplement_Layouts

open Matrix

namespace PNormReg

namespace Supplement

/-- **Theorem 3** (High-accuracy `ℓ_p`-regression for `p ∈ (1, 2]`).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…), Theorem 3, p.2 (PDF p.3); problem (1) and footnotes 1–2, p.1; `Λ_p`, p.27.

"For p ∈ (1, 2] and ϵ, δ ∈ (0, 1), there is an algorithm which returns a (1 + ϵ)-approximate solution
to (1), with probability at least 1 − δ, in time Õ_p(nnz(A) + d^ω)."

For every `τ > 0` there are one admissible program `P` and constants `C > 0`, `K ∈ ℕ` such that for all
`n`, `d ≥ 1`, full column rank `A`, `b`, `p ∈ (1, 2]` and `ϵ, δ ∈ (0, 1)`, with
`T = C·(2/(p−1))^{K/(p−1)}·(nnz(A) + n^τ·d^ω)·(log(2 + n + 1/ϵ + 1/δ))^K`: every coin tape halts with
`work ≤ T`, and a measurable set of tapes of probability at least `1 − δ` gives a halted output `x̂` with
`∥Ax̂ − b∥_p ≤ (1 + ϵ)∥Ax − b∥_p` for all `x`.

**Formalization Note.**
* `Õ_p`: footnote 2 says the hidden `p`-factors are "exponential in 1/(p−1) for Theorem 3; see
  Section 4", and p.27 makes it precise: the only non-polynomial factor is `Λ_p = (p4^p/(p−1))^{1/(p−1)}`,
  with `log Λ_p = O((p−1)^{−1} log(2/(p−1)))`. The factor `(2/(p−1))^{K/(p−1)}` is that bound, with one
  `K` for all `p ∈ (1, 2]`; it covers `Λ_p ≤ (2/(p−1))^{5/(p−1)}` and every polynomial in `1/(p−1)`.
* `n^τ` (footnote 2's `n^{o(1)}` from fast matrix multiplication) multiplies only `d^ω`.
* Input: `sparseInput [p, ϵ, δ] A b` (the nonzero entries of `A`, then `b`): a dense matrix could not
  be read in `nnz(A)` time. `nnz(A) = sparsity(A) + n + d` (p.7).
* Machine, coin tape, `∀ τ` first, success event and `∀ x` for `f⋆` as in `PNormReg.theorem_2`. -/
theorem theorem_3 :
    ∀ τ : ℝ, 0 < τ →
      ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d : ℕ), 1 ≤ d → ∀ (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
          Function.Injective A.mulVec →
          ∀ p ε δ : ℝ, 1 < p → p ≤ 2 → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P (sparseInput [p, ε, δ] A b) ω t).halted = true ∧
              ((run P (sparseInput [p, ε, δ] A b) ω t).work : ℝ) ≤
                C * (2 / (p - 1)) ^ ((K : ℝ) / (p - 1)) *
                  ((nnz A : ℝ) + (n : ℝ) ^ τ *
                    (d : ℝ) ^ OAI.MatrixMultiplication.Arithmetic.omega ℝ) *
                  Real.log (2 + n + 1 / ε + 1 / δ) ^ K) ∧
            ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - δ ≤ (coinTape E).toReal ∧
              ∀ ω ∈ E, ∀ t : ℕ, (run P (sparseInput [p, ε, δ] A b) ω t).halted = true →
                ∀ x : Fin d → ℝ,
                  lpNorm p (A *ᵥ outputVec d (run P (sparseInput [p, ε, δ] A b) ω t) - b) ≤
                    (1 + ε) * lpNorm p (A *ᵥ x - b) := by sorry

end Supplement

end PNormReg
