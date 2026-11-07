-- Prove2me | Theorems.Thm_PsdPermanent_theorem_1
-- name    : PsdPermanent.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:37.170228+00:00
-- url     : https://prove2.me/theorems/04fb7f8c-dcbe-4ff2-9c54-6142ab98ec69
-- title:
--   Theorem 1 — $e^{-\gamma n}\widehat P(A)\le\mathrm{per}(A)\le\widehat P(A)$ and a polynomial-time $e^{(\gamma+\varepsilon)n}$-approximation
-- statement:
--   Let $A\succeq0$ be an $n\times n$ Hermitian matrix, let $V$ be a full column rank factor with $A=VV^\dagger$, and let $\widehat P(A)=\exp(\Phi(V))$, with the convention $\widehat P(A)=0$ if $A$ has a zero diagonal entry. Here $\Phi(V)=\max\{\sum_i\log(v_i^\dagger Xv_i)+\log\det X-\operatorname{tr}X+d\mid X\succ0\}$, and $\gamma$ is the Euler–Mascheroni constant. Such a factor exists, and
--   $$e^{-\gamma n}\widehat P(A)\le\mathrm{per}(A)\le\widehat P(A).$$
--   Moreover there is a single deterministic Turing machine, polynomial time in the length of its binary input, which given rational $A$ and rational $\varepsilon$ outputs a rational $Q$ such that, whenever $\varepsilon>0$ and $A$ is Hermitian positive semidefinite,
--
--   1. $\widehat P(A)\le Q\le e^{\varepsilon n}\widehat P(A)$;
--   2. $e^{-(\gamma+\varepsilon)n}Q\le\mathrm{per}(A)\le Q$.
--
--   Combined with the cited hardness of approximation below $e^{(\gamma-\varepsilon)n}$, this identifies the deterministic polynomial-time approximation ratio of the PSD permanent at the exponential scale.
--
--   **Formalization Note** All $n\ge0$ are covered, and the first display holds for every full column rank factor. In the machine, $\varepsilon$ is an input, so one machine serves every rational $\varepsilon>0$.
--
--   Differences from the source:
--   - encoding: P̂(A), a function of A → Phat A V for a factor V, with the bounds for every full column rank factor and the existence of one with d = rank A; reason: Φ is defined on factors; this covers every choice the paper allows
--   - encoding: per(A) = ∑_σ ∏_i A_{i,σ(i)}, a real number on PSD A → Mathlib permanent ∑_σ ∏_i A_{σ(i),i} in ℂ, with imaginary part stated to vanish; reason: reindexing by σ⁻¹ gives the same value; Lean types the entries as complex
--   - encoding: H_d^{++} for d ≥ 1 (§3) → n = 0 and d = 0 allowed, with the empty matrix positive definite, det = 1 and per = 1; reason: Theorem 1 says every n × n Hermitian A ⪰ 0; the empty-product conventions make n = 0 an exact equality, and A = 0 with n ≥ 1 is governed by the zero-diagonal convention
--   - reading: deterministic polynomial time in the standard finite-precision model → Turing.TM2ComputableInPolyTime with a binary input encoding; reason: the standard meaning of polynomial in the input size for rational input
--   - reading: for every ε > 0 an algorithm, polynomial in log(1/ε) → one machine with rational ε as input; a real ε is served by any rational ε′ ∈ (0, ε]; reason: a time bound naming log(1/ε) only makes sense with ε as an input, and this is the stronger reading
--   - reading: outputs a number Q(A) → a rational, written in binary; reason: a machine writes a finite string; exp(Φ̃ + εn/2) in the proof is not one
--   - reading: Q(A) ≤ e^{Φ(A)+εn/2} in the proof of Theorem 9 → Q ≤ e^{εn} P̂; reason: the second half of the slack pays for rational rounding; the proof itself says to replace ε/2 by ε, and ε is arbitrary, so the family is the same
--   - generalization: given a rational Hermitian positive semidefinite matrix and ε > 0 → the machine halts in polynomial time on every instance; the output is constrained only on valid ones; reason: valid inputs are a subset of all instances, so this specializes to the source
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 1, p.1

import Mathlib
import Definitions.Def_PsdPermanent_IsGramFactor
import Definitions.Def_PsdPermanent_Phat
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_PsdPermanent_RatInstance
import Definitions.Def_PsdPermanent_encInstance
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **Theorem 1 (Main theorem).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 1, p.1: "Let A ⪰ 0 be an n × n Hermitian matrix, and let P̂(A) = exp(Φ(V)), with the convention P̂(A) = 0 if A has a zero
diagonal entry. Then e^{−γn} P̂(A) ≤ per(A) ≤ P̂(A). Moreover, for every ε > 0, P̂(A) can be approximated in deterministic polynomial time
well enough to return an e^{(γ+ε)n}-approximation to per(A)."

The first clause is `PsdPermanent.theorem_7`. The second gives one Turing machine with both guarantees on the same output `Q`: `P̂ ≤ Q ≤ e^{εn} P̂`,
and `e^{−(γ+ε)n} Q ≤ per(A) ≤ Q`.

**Formalization Note.** `γ` is `Real.eulerMascheroniConstant`. `Phat` takes a factor as an argument, and the bounds hold for every full column rank
factor, of which one with `d = rank A` exists. `per(A)` is complex in Lean, so its imaginary part is stated to vanish. Polynomial time is
`Turing.TM2ComputableInPolyTime` for the binary encoding `PsdPermanent.encInstance` and output `OnlineCRS.Combine.encRat`; `f` comes before
the instance and `ε` is an input, so one machine serves every rational `ε > 0` and every rational `A`. The machine halts in polynomial time on every
input; its output is constrained only when `0 < ε` and `A` is positive semidefinite. -/
theorem theorem_1 :
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef →
      (∃ V : Matrix (Fin n) (Fin A.rank) ℂ, IsGramFactor A V) ∧
        ∀ (d : ℕ) (V : Matrix (Fin n) (Fin d) ℂ), IsGramFactor A V →
          A.permanent.im = 0 ∧
            Real.exp (-(Real.eulerMascheroniConstant * n)) * Phat A V ≤ A.permanent.re ∧
            A.permanent.re ≤ Phat A V) ∧
      ∃ f : RatInstance → ℚ,
        Nonempty (Turing.TM2ComputableInPolyTime encInstance OnlineCRS.Combine.encRat f) ∧
        ∀ I : RatInstance, 0 < I.eps → I.matrix.PosSemidef →
          I.matrix.permanent.im = 0 ∧
            Real.exp (-((Real.eulerMascheroniConstant + (I.eps : ℝ)) * I.n)) * (f I : ℝ) ≤ I.matrix.permanent.re ∧
            I.matrix.permanent.re ≤ (f I : ℝ) ∧
            ∀ (d : ℕ) (V : Matrix (Fin I.n) (Fin d) ℂ), IsGramFactor I.matrix V →
              Phat I.matrix V ≤ (f I : ℝ) ∧ (f I : ℝ) ≤ Real.exp ((I.eps : ℝ) * I.n) * Phat I.matrix V := by sorry

end PsdPermanent
