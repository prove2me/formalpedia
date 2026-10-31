-- Prove2me | Theorems.Thm_RobustToDynamics_step1_lyapunov_polytime
-- name    : RobustToDynamics.step1_lyapunov_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:52.855246+00:00
-- url     : https://prove2.me/theorems/bd094976-2418-4a5f-8cb9-ab5fd413f8f2
-- title:
--   Step 1 — the Lyapunov solution $M$ of (2.14) is rational and computable in time polynomial in $\sigma(G)$
-- statement:
--   There is an algorithm that, given a rational matrix $G\in\mathbb Q^{n\times n}$ in binary, runs in time polynomial in the length of its input and, whenever $\rho(G)<1$, outputs $n^2$ rational numbers which, read row by row as a matrix $M\in\mathbb Q^{n\times n}$, solve
--   $$
--   G^TMG-M=-I .
--   $$
--   In particular the solution $M$ of (2.14) is rational and has size polynomially bounded by $\sigma(G)$ (an algorithm running in polynomial time writes an output of polynomial length). By uniqueness (Step 1), this output is the Lyapunov matrix of the proof.
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13. The output is the list of entries $M_{ij}$ in row-major order (entry $i n+j$).
--
--   Differences from the source:
--   - encoding: computable in time polynomial in the size σ (standard Turing model) → Nonempty (Turing.TM2ComputableInPolyTime ea eb f) with binary encodings over Fin 4; reason: Mathlib's Turing-machine model; the encodings write every number in binary (rationals in lowest terms) with dimensions first, so their length is polynomially related to σ
--   - encoding: the algorithm is run on instances satisfying the hypotheses → a total function computed in polynomial time on every encoded input, constrained only under the hypotheses; reason: a polynomial-time machine must halt on every input; constraining its output only on the instances the source speaks about changes no instance
--   - encoding: M has size polynomially bounded by σ(G) → no separate conjunct: implied by the polynomial running time; reason: a machine running in time T writes at most T output symbols
--   - encoding: the matrix M → its n² entries as a row-major list of rationals; reason: a fixed reading of the output list as a matrix; same matrix
--   - encoding: ρ(G) = max of |λ| over the (real or complex) eigenvalues → specRadius, the supremum of |z| over the complex spectrum; reason: the complex spectrum of an n × n matrix is finite and nonempty for n ≥ 1, so the supremum is the maximum; same value
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 1, p.14

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_RobustToDynamics_SqMatQ
import Definitions.Def_RobustToDynamics_encSqMat
import Definitions.Def_RobustToDynamics_encListRat

open Matrix

namespace RobustToDynamics

/-- **Step 1: the Lyapunov solution `M` is rational and computable in polynomial time.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 1, p.14: "Note that M is rational, can be computed in polynomial time, and has size
polynomially bounded by σ(G)."

There is a function `f`, computable by a Turing machine in time polynomial in the length of the
binary encoding of `G ∈ ℚ^{n×n}`, such that for every rational `G` with `ρ(G) < 1` the output
`f G` is a list of `n²` rationals which, read row by row as a matrix `M ∈ ℚ^{n×n}`
(`M i j` = entry `i·n + j`), solves `GᵀMG − M = −I`.

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with input encoding
`encSqMat` (binary, `σ(G)`-sized) and output encoding `encListRat`; the machine must halt in
polynomial time on every input, and its output is constrained only when `ρ(G) < 1`. Polynomial
output length gives the size bound. With `step1_lyapunov_solution` the output is the unique
solution `M` of (2.14). `ρ(G)` is `specRadius` of `G` cast to `ℝ`. -/
theorem step1_lyapunov_polytime :
    ∃ f : SqMatQ → List ℚ,
      Nonempty (Turing.TM2ComputableInPolyTime encSqMat encListRat f) ∧
      ∀ s : SqMatQ, specRadius (s.G.map (Rat.cast : ℚ → ℝ)) < 1 →
        (f s).length = s.n * s.n ∧
        s.Gᵀ * (Matrix.of fun i j : Fin s.n => (f s).getD ((i : ℕ) * s.n + (j : ℕ)) 0) * s.G -
            (Matrix.of fun i j : Fin s.n => (f s).getD ((i : ℕ) * s.n + (j : ℕ)) 0) = -1 := by sorry

end RobustToDynamics
