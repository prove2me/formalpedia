-- Prove2me | Theorems.Thm_PNormReg_Supplement_theorem_7
-- name    : PNormReg.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:56:42.936718+00:00
-- url     : https://prove2.me/theorems/d71a8073-b3bf-4451-8360-391122a27775
-- title:
--   Theorem 7, p.11 — approximate $\ell_p$-regression for $p\in[2,\infty]$ in time $\widetilde O_p(nd^{\omega-1}+nd\epsilon^{-2})$, and $\widetilde O(nd^{\omega-1}+nd\epsilon^{-2})$ at $p=\infty$
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ have full column rank, $b\in\mathbb R^n$, $p\in[2,\infty]$ and $\epsilon,\delta\in(0,1)$. There is an algorithm that finds a $(1+\epsilon)$-approximate solution of $\min_x\|Ax-b\|_p$ with probability at least $1-\delta$ in time $\widetilde O_p(nd^{\omega-1}+nd\epsilon^{-2})$ for finite $p$, and $\widetilde O(nd^{\omega-1}+nd\epsilon^{-2})$ for $p=\infty$. Precisely, with $L=\log(2+n+1/\epsilon+1/\delta)$, for every $\tau>0$:
--
--   1. (finite $p$) one program and $C>0$, $K\in\mathbb N$ serve every $p\ge2$, halting on every coin sequence within $C\,p^K\big(n^{1+\tau}d^{\omega-1}+nd\epsilon^{-2}\big)L^K$ steps, and with probability at least $1-\delta$ returning $\hat x$ with $\|A\hat x-b\|_p\le(1+\epsilon)\|Ax-b\|_p$ for all $x$;
--   2. ($p=\infty$) one program and $C>0$, $K\in\mathbb N$ halting within $C\big(n^{1+\tau}d^{\omega-1}+nd\epsilon^{-2}\big)L^K$ steps, and with probability at least $1-\delta$ returning $\hat x$ with $\|A\hat x-b\|_\infty\le(1+\epsilon)\|Ax-b\|_\infty$ for all $x$.
--
--   Together with Theorem 4 and Theorem 6 this is the paper's low-accuracy algorithm; it implies Theorem 1.
--
--   **Formalization Note** Finite $p$ uses the base mission's input layout (real memory $p,\epsilon,\delta$, $A$, $b$); $p=\infty$ uses the dense layout with real memory $\epsilon,\delta$, $A$, $b$.
--
--   Differences from the source:
--   - reading: "there is an algorithm" (no machine named) → one finite admissible program of PNormReg.Machine per clause (finite p; p = ∞); reason: the paper fixes no machine; same reading as the published goal Theorem 2
--   - reading: Õ(·) (footnote 2: n^{o(1)} from fast matrix multiplication and polylog factors in n, d, 1/ϵ, 1/δ) → for every τ > 0 one program with constants C, K: n^τ on the fast-matrix-multiplication term only, (log(2 + n + 1/ϵ + 1/δ))^K on the whole bound; reason: footnote 2 pins the hidden factors; same reading as Theorem 2
--   - reading: Õ_p for finite p ≥ 2 (footnote 2: polynomial in p) → factor p^K, one program for every p ≥ 2; reason: footnote 2; same reading as Theorem 2
--   - encoding: input of problem (1) → finite p: the base goalInput (p, ϵ, δ, A, b); p = ∞: dense layout (ϵ, δ, A, b); reason: the paper names no format
--   - encoding: with probability at least 1 − δ; f⋆_p = min_x f_p(x) → a measurable set of fair-coin tapes of probability ≥ 1 − δ on which the halted output satisfies the bound against every x; reason: the minimum exists, so "for every x" is the same condition; same as Theorem 2
--   - encoding: A ∈ ℝ^{n×d} (d ≥ 1 implicit) → 1 ≤ d; reason: excludes only the empty problem, where a zero time bound would forbid halting
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 7, p.11 (PDF p.12); problem (1) and footnotes 1–2, p.1

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PNormReg_Supplement_Layouts

open Matrix

namespace PNormReg

namespace Supplement

/-- **Theorem 7** (Approximate `ℓ_p`-regression), both clauses.

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…), Theorem 7, p.11 (PDF p.12); problem (1) and footnotes 1–2, p.1.

"Let p ∈ [2, ∞] and ϵ, δ ∈ (0, 1). There is an algorithm that finds a (1 + ϵ)-approximate solution to (1)
with probability at least 1 − δ in time Õ_p(nd^{ω−1} + ndϵ^{−2}) for finite p, and Õ(nd^{ω−1} + ndϵ^{−2})
for p = ∞."

1. Finite `p`: for every `τ > 0` there are one admissible program and `C > 0`, `K ∈ ℕ` such that for
   all `n`, `d ≥ 1`, full column rank `A`, `b`, `p ≥ 2`, `ϵ, δ ∈ (0, 1)`, every coin tape halts with
   `work ≤ C·p^K·(n^{1+τ}d^{ω−1} + ndϵ^{−2})·(log(2 + n + 1/ϵ + 1/δ))^K`, and with probability at least
   `1 − δ` the output `x̂` has `∥Ax̂ − b∥_p ≤ (1 + ϵ)∥Ax − b∥_p` for all `x`.
2. `p = ∞`: the same with `work ≤ C·(n^{1+τ}d^{ω−1} + ndϵ^{−2})·(log(2 + n + 1/ϵ + 1/δ))^K` (no `p`
   factor) and `∥·∥_∞`.

**Formalization Note.**
* `Õ_p` for `p ≥ 2` is `p^K` (footnote 2: "polynomial in p for our p ≥ 2 results"), as in
  `PNormReg.theorem_2`; the `p = ∞` clause has no `p` factor.
* `n^τ` (footnote 2's `n^{o(1)}` from fast matrix multiplication) multiplies only `nd^{ω−1}`.
* Inputs: finite `p` uses the base mission's `goalInput A b p ϵ δ`; `p = ∞` uses
  `denseInput [ϵ, δ] A b`. The two clauses may use different programs.
* Machine, coin tape, `∀ τ` first, success event and `∀ x` for `f⋆` as in `PNormReg.theorem_2`. -/
theorem theorem_7 :
    (∀ τ : ℝ, 0 < τ →
      ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d : ℕ), 1 ≤ d → ∀ (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
          Function.Injective A.mulVec →
          ∀ p ε δ : ℝ, 2 ≤ p → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P (goalInput A b p ε δ) ω t).halted = true ∧
              ((run P (goalInput A b p ε δ) ω t).work : ℝ) ≤
                C * p ^ K *
                  ((n : ℝ) ^ (1 + τ) *
                      (d : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ - 1) +
                    n * d * ε ^ (-2 : ℝ)) *
                  Real.log (2 + n + 1 / ε + 1 / δ) ^ K) ∧
            ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - δ ≤ (coinTape E).toReal ∧
              ∀ ω ∈ E, ∀ t : ℕ, (run P (goalInput A b p ε δ) ω t).halted = true →
                ∀ x : Fin d → ℝ,
                  lpNorm p (A *ᵥ outputVec d (run P (goalInput A b p ε δ) ω t) - b) ≤
                    (1 + ε) * lpNorm p (A *ᵥ x - b)) ∧
    (∀ τ : ℝ, 0 < τ →
      ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d : ℕ), 1 ≤ d → ∀ (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
          Function.Injective A.mulVec →
          ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P (denseInput [ε, δ] A b) ω t).halted = true ∧
              ((run P (denseInput [ε, δ] A b) ω t).work : ℝ) ≤
                C * ((n : ℝ) ^ (1 + τ) *
                      (d : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ - 1) +
                    n * d * ε ^ (-2 : ℝ)) *
                  Real.log (2 + n + 1 / ε + 1 / δ) ^ K) ∧
            ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - δ ≤ (coinTape E).toReal ∧
              ∀ ω ∈ E, ∀ t : ℕ, (run P (denseInput [ε, δ] A b) ω t).halted = true →
                ∀ x : Fin d → ℝ,
                  linfNorm (A *ᵥ outputVec d (run P (denseInput [ε, δ] A b) ω t) - b) ≤
                    (1 + ε) * linfNorm (A *ᵥ x - b)) := by sorry

end Supplement

end PNormReg
