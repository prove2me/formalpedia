-- Prove2me | Theorems.Thm_RobustToDynamics_rational_linear_system_polytime
-- name    : RobustToDynamics.rational_linear_system_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:50.344008+00:00
-- url     : https://prove2.me/theorems/0f56fb6e-fbe8-493b-b4d8-3d363df35129
-- title:
--   [47], cited p.13 — a solvable rational linear system has a solution computable in polynomial time
-- statement:
--   There is an algorithm that, given a rational linear system $Ax=b$ with $A\in\mathbb Q^{p\times q}$, $b\in\mathbb Q^p$ in binary, runs in time polynomial in the length of its input and, whenever the system has a solution, outputs $q$ rationals $x_1,\dots,x_q$ with $Ax=b$.
--
--   In particular every solvable rational system has a solution of size polynomially bounded by the size of $(A,b)$. The proof of Theorem 2.7 uses it to compute the Lyapunov matrices $M$ and $\hat M$ from the linear equations (2.14). The paper cites this fact from Schrijver's *Theory of Linear and Integer Programming* [47].
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13.
--
--   Differences from the source:
--   - encoding: computable in time polynomial in the size σ (standard Turing model) → Nonempty (Turing.TM2ComputableInPolyTime ea eb f) with binary encodings over Fin 4; reason: Mathlib's Turing-machine model; the encodings write every number in binary (rationals in lowest terms) with dimensions first, so their length is polynomially related to σ
--   - encoding: the algorithm is run on instances satisfying the hypotheses → a total function computed in polynomial time on every encoded input, constrained only under the hypotheses; reason: a polynomial-time machine must halt on every input; constraining its output only on the instances the source speaks about changes no instance
--   - encoding: the solution has size polynomially bounded by the size of the data → no separate conjunct: implied by the polynomial running time; reason: a machine running in time T writes at most T output symbols
--   - encoding: the system has a solution → ∃ x ∈ ℚ^q with Ax = b; reason: for rational data solvability over ℚ and over ℝ coincide
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, p.13 (cited from [47])

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_RobustToDynamics_LinSys
import Definitions.Def_RobustToDynamics_encLinSys
import Definitions.Def_RobustToDynamics_encListRat

open Matrix

namespace RobustToDynamics

/-- **Rational linear systems are solvable in polynomial time ([47], cited on p.13).**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, p.13: "any system of
rational linear equations has a solution of size polynomially bounded by the size of the data
defining the equality system [47]. In addition, this solution can be computed in polynomial time."

There is a function `f`, computable by a Turing machine in time polynomial in the length of the
binary encoding of `(A, b)`, such that for every rational system `Ax = b` (`A ∈ ℚ^{p×q}`) that has a
solution, `f (A, b)` is a list of `q` rationals solving it.

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with input encoding
`encLinSys` and output encoding `encListRat`; the machine halts in polynomial time on every input,
and its output is constrained only on solvable systems. A polynomial-time output has polynomial
size, which is the paper's size bound. Solvability is over `ℚ` (equivalent to solvability over `ℝ`
for rational data). The entry `j` of the output vector is `(f s).getD j 0`. -/
theorem rational_linear_system_polytime :
    ∃ f : LinSys → List ℚ,
      Nonempty (Turing.TM2ComputableInPolyTime encLinSys encListRat f) ∧
      ∀ s : LinSys, (∃ x : Fin s.q → ℚ, s.A *ᵥ x = s.b) →
        (f s).length = s.q ∧ s.A *ᵥ (fun j : Fin s.q => (f s).getD j 0) = s.b := by sorry

end RobustToDynamics
