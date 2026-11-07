-- Prove2me | Theorems.Thm_PsdPermanent_theorem_9
-- name    : PsdPermanent.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:49.298411+00:00
-- url     : https://prove2.me/theorems/6f2281fc-1198-43bf-a2fa-600bc358daf1
-- title:
--   Theorem 9 — the algorithm: $e^{-(\gamma+\varepsilon)n}Q(A)\le\mathrm{per}(A)\le Q(A)$
-- statement:
--   There is a single deterministic Turing machine which, given a rational matrix $A\in\mathbb C^{n\times n}$ and a rational $\varepsilon$, halts in time polynomial in the length of the binary input and outputs a rational $Q(A)$ such that, whenever $\varepsilon>0$ and $A$ is Hermitian positive semidefinite,
--   $$e^{-(\gamma+\varepsilon)n}Q(A)\le\mathrm{per}(A)\le Q(A).$$
--
--   The length of the input bounds both $n$ and $\log(1/\varepsilon)$. This is the deterministic $e^{(\gamma+\varepsilon)n}$-approximation of the PSD permanent.
--
--   Differences from the source:
--   - reading: deterministic polynomial time in the standard finite-precision model → Turing.TM2ComputableInPolyTime with a binary input encoding; reason: the standard meaning of polynomial in the input size for rational input
--   - reading: for every ε > 0 an algorithm, polynomial in log(1/ε) → one machine with rational ε as input; a real ε is served by any rational ε′ ∈ (0, ε]; reason: a time bound naming log(1/ε) only makes sense with ε as an input, and this is the stronger reading
--   - reading: outputs a number Q(A) → a rational, written in binary; reason: a machine writes a finite string; exp(Φ̃ + εn/2) in the proof is not one
--   - generalization: given a rational Hermitian positive semidefinite matrix and ε > 0 → the machine halts in polynomial time on every instance; the output is constrained only on valid ones; reason: valid inputs are a subset of all instances, so this specializes to the source
--   - encoding: per(A) = ∑_σ ∏_i A_{i,σ(i)}, a real number on PSD A → Mathlib permanent ∑_σ ∏_i A_{σ(i),i} in ℂ, with imaginary part stated to vanish; reason: reindexing by σ⁻¹ gives the same value; Lean types the entries as complex
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 9, p.9

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_PsdPermanent_RatInstance
import Definitions.Def_PsdPermanent_encInstance
open Matrix
open scoped ComplexOrder

namespace PsdPermanent

/-- **Theorem 9 (Algorithmic form).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Theorem 9, p.9: "For every ε > 0, there is a deterministic algorithm which, given a rational Hermitian positive semidefinite matrix
A ∈ C^{n×n}, runs in time polynomial in the input size, n, and log(1/ε), and outputs a number Q(A) such that e^{−(γ+ε)n} Q(A) ≤ per(A) ≤
Q(A)."

**Formalization Note.** One Turing machine for all rational `ε > 0` and all rational `A`; see `PsdPermanent.machine_core`. Its time is
polynomial in the length of `encInstance I`, which bounds both `n` and `log(1/ε)` (`PsdPermanent.encInstance`). A real `ε > 0` is served by
any rational `ε' ∈ (0, ε]`, since the bound is monotone in `ε`. -/
theorem theorem_9 :
    ∃ f : RatInstance → ℚ,
      Nonempty (Turing.TM2ComputableInPolyTime encInstance OnlineCRS.Combine.encRat f) ∧
      ∀ I : RatInstance, 0 < I.eps → I.matrix.PosSemidef →
        I.matrix.permanent.im = 0 ∧
          Real.exp (-((Real.eulerMascheroniConstant + (I.eps : ℝ)) * I.n)) * (f I : ℝ) ≤ I.matrix.permanent.re ∧
          I.matrix.permanent.re ≤ (f I : ℝ) := by sorry

end PsdPermanent
