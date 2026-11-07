-- Prove2me | Theorems.Thm_PsdPermanent_theorem_7
-- name    : PsdPermanent.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:43.219708+00:00
-- url     : https://prove2.me/theorems/d07f8e1c-fe35-41d1-95ea-4645c8eb0a4b
-- title:
--   Theorem 7 — the entropic sandwich $e^{-\gamma n}\widehat P(A)\le\mathrm{per}(A)\le\widehat P(A)$
-- statement:
--   For every $n\times n$ Hermitian matrix $A\succeq0$, a full column rank Gram factor with $d=\operatorname{rank}A$ exists, $\mathrm{per}(A)$ is real, and
--   $$e^{-\gamma n}\widehat P(A)\le\mathrm{per}(A)\le\widehat P(A),$$
--   where $\gamma$ is the Euler–Mascheroni constant.
--
--   This is the exact sandwich underlying the approximation algorithm.
--
--   **Formalization Note** The bounds are stated for every full column rank Gram factor $V$, since $\widehat P$ takes the factor as an argument. All $n\ge0$ are covered.
--
--   Differences from the source:
--   - encoding: P̂(A), a function of A → Phat A V for a factor V, with the bounds for every full column rank factor and the existence of one with d = rank A; reason: Φ is defined on factors; this covers every choice the paper allows
--   - encoding: per(A) = ∑_σ ∏_i A_{i,σ(i)}, a real number on PSD A → Mathlib permanent ∑_σ ∏_i A_{σ(i),i} in ℂ, with imaginary part stated to vanish; reason: reindexing by σ⁻¹ gives the same value; Lean types the entries as complex
--   - encoding: H_d^{++} for d ≥ 1 (§3) → n = 0 and d = 0 allowed, with the empty matrix positive definite, det = 1 and per = 1; reason: Theorem 1 says every n × n Hermitian A ⪰ 0; the empty-product conventions make n = 0 an exact equality, and A = 0 with n ≥ 1 is governed by the zero-diagonal convention
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 7, p.7

import Mathlib
import Definitions.Def_PsdPermanent_IsGramFactor
import Definitions.Def_PsdPermanent_Phat
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **Theorem 7 (Entropic sandwich).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 7, p.7: "For every Hermitian A ⪰ 0, e^{−γn} P̂(A) ≤ per(A) ≤ P̂(A)."

**Formalization Note.** A factor of the paper's shape exists (`d = rank A`), and the bounds hold for every factor, since `Phat`
takes the factor as an argument. `per(A)` is complex in Lean, so its imaginary part is stated to vanish. All `n` are covered,
including `n = 0` (`Phat = 1 = per`) and zero diagonals (`Phat = 0 = per`). -/
theorem theorem_7 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    (∃ V : Matrix (Fin n) (Fin A.rank) ℂ, IsGramFactor A V) ∧
      ∀ (d : ℕ) (V : Matrix (Fin n) (Fin d) ℂ), IsGramFactor A V →
        A.permanent.im = 0 ∧
          Real.exp (-(Real.eulerMascheroniConstant * n)) * Phat A V ≤ A.permanent.re ∧
          A.permanent.re ≤ Phat A V := by sorry

end PsdPermanent
