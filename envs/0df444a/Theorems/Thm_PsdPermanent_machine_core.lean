-- Prove2me | Theorems.Thm_PsdPermanent_machine_core
-- name    : PsdPermanent.machine_core
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:42.04652+00:00
-- url     : https://prove2.me/theorems/a80d3524-ddc2-4397-a036-36dfc35ac0a7
-- title:
--   Proof of Theorem 9, p.9 — one machine with $\widehat P(A)\le Q\le e^{\varepsilon n}\widehat P(A)$
-- statement:
--   There is a single deterministic Turing machine which, given a rational matrix $A$ and a rational $\varepsilon$, halts in time polynomial in the length of the binary input and outputs a rational $Q$ such that, whenever $\varepsilon>0$ and $A$ is Hermitian positive semidefinite,
--   $$\widehat P(A)\le Q\le e^{\varepsilon n}\widehat P(A).$$
--
--   In particular $Q=0$ on a zero diagonal and $Q=1$ at $n=0$. This is the statement "$\widehat P(A)$ can be approximated in deterministic polynomial time".
--
--   Differences from the source:
--   - reading: deterministic polynomial time in the standard finite-precision model → Turing.TM2ComputableInPolyTime with a binary input encoding; reason: the standard meaning of polynomial in the input size for rational input
--   - reading: for every ε > 0 an algorithm, polynomial in log(1/ε) → one machine with rational ε as input; a real ε is served by any rational ε′ ∈ (0, ε]; reason: a time bound naming log(1/ε) only makes sense with ε as an input, and this is the stronger reading
--   - reading: outputs a number Q(A) → a rational, written in binary; reason: a machine writes a finite string; exp(Φ̃ + εn/2) in the proof is not one
--   - reading: Q(A) ≤ e^{Φ(A)+εn/2} in the proof of Theorem 9 → Q ≤ e^{εn} P̂; reason: the second half of the slack pays for rational rounding; the proof itself says to replace ε/2 by ε, and ε is arbitrary, so the family is the same
--   - generalization: given a rational Hermitian positive semidefinite matrix and ε > 0 → the machine halts in polynomial time on every instance; the output is constrained only on valid ones; reason: valid inputs are a subset of all instances, so this specializes to the source
--   - encoding: P̂(A), a function of A → Phat A V for a factor V, with the bounds for every full column rank factor and the existence of one with d = rank A; reason: Φ is defined on factors; this covers every choice the paper allows
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), proof of Theorem 9, p.9; Theorem 1, p.1

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

/-- **The machine approximates P̂.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), proof of Theorem 9, p.9: "If A has a zero diagonal entry, output 0. Otherwise compute a sufficiently accurate numerical
full-rank Gram factor V, and solve the concave program Eq. (4) to additive accuracy at most εn/2." and "Then Q(A) ≥ e^{Φ(A)} = P̂(A)
≥ per(A)."; Theorem 1, p.1: "P̂(A) can be approximated in deterministic polynomial time".

One Turing machine, polynomial time in the length of the binary input, with `P̂ ≤ Q ≤ e^{εn} P̂` on every rational positive
semidefinite matrix and rational `ε > 0`.

**Formalization Note.** `f` comes before the instance and `ε` is part of the instance: one machine for all `ε`. The output is the
rational `f I`, written by `OnlineCRS.Combine.encRat`, because a machine writes a finite string and the proof's `exp(Φ̃ + εn/2)` is
not one. The window `e^{εn}` rather than the proof's `e^{εn/2}`: the other half pays for rounding, and since `ε` is arbitrary it
is the same family. The machine halts in polynomial time on every instance; its output is constrained only on valid ones. At
`n = 0` the window forces `Q = 1`, on a zero diagonal `Q = 0`. -/
theorem machine_core :
    ∃ f : RatInstance → ℚ,
      Nonempty (Turing.TM2ComputableInPolyTime encInstance OnlineCRS.Combine.encRat f) ∧
      ∀ I : RatInstance, 0 < I.eps → I.matrix.PosSemidef →
        ∀ (d : ℕ) (V : Matrix (Fin I.n) (Fin d) ℂ), IsGramFactor I.matrix V →
          Phat I.matrix V ≤ (f I : ℝ) ∧ (f I : ℝ) ≤ Real.exp ((I.eps : ℝ) * I.n) * Phat I.matrix V := by sorry

end PsdPermanent
