-- Prove2me | Theorems.Thm_RobustToDynamics_lp_polytime
-- name    : RobustToDynamics.lp_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:39.082123+00:00
-- url     : https://prove2.me/theorems/5bd9cc19-c5c9-47b0-99f8-1b2128e3afcb
-- title:
--   [47], cited pp.13, 16 — a rational LP with an optimal solution has one computable in polynomial time
-- statement:
--   There is an algorithm that, given a linear program
--   $$
--   \min\{c^Tx : x\in\mathbb R^q,\ Ax\le b\}
--   $$
--   with rational data $A\in\mathbb Q^{p\times q}$, $b\in\mathbb Q^p$, $c\in\mathbb Q^q$ in binary, runs in time polynomial in the length of its input and, whenever the LP has an optimal solution, outputs $q$ rationals forming an optimal solution.
--
--   The proof of Theorem 2.7 uses it for the box bounds $l_i,u_i$ of (2.16) and for the final linear program over $\mathcal S_r$. The paper cites it from [47].
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13.
--
--   Differences from the source:
--   - encoding: computable in time polynomial in the size σ (standard Turing model) → Nonempty (Turing.TM2ComputableInPolyTime ea eb f) with binary encodings over Fin 4; reason: Mathlib's Turing-machine model; the encodings write every number in binary (rationals in lowest terms) with dimensions first, so their length is polynomially related to σ
--   - encoding: the algorithm is run on instances satisfying the hypotheses → a total function computed in polynomial time on every encoded input, constrained only under the hypotheses; reason: a polynomial-time machine must halt on every input; constraining its output only on the instances the source speaks about changes no instance
--   - reading: any linear function cᵀx can be optimized over a polyhedron in polynomial time → an optimal solution is output whenever one exists; reason: the proof uses exactly this (every LP it solves has an optimal solution), and it is not a weaker claim: the LP min 0 s.t. Ax ≤ b has an optimum iff Ax ≤ b is feasible, so checking the output decides feasibility, and an optimum exists iff the primal and the dual system are both feasible; full LP solving (infeasible / unbounded / optimal) thus reduces to this statement in polynomial time
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, p.13 and p.16 (cited from [47])

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_RobustToDynamics_IsMinimizer
import Definitions.Def_RobustToDynamics_LPInst
import Definitions.Def_RobustToDynamics_encLP
import Definitions.Def_RobustToDynamics_encListRat

open Matrix

namespace RobustToDynamics

/-- **Linear programs with rational data are solvable in polynomial time ([47], cited on
pp.13 and 16).**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, p.13: "if a linear program
defined by rational data has an optimal solution, then it has one with size polynomial in the data
defining the LP", and p.16: "any linear function cT x can be optimized over a polyhedron in
polynomial time".

There is a function `f`, computable by a Turing machine in time polynomial in the length of the
binary encoding of `(A, b, c)`, such that for every rational linear program
`min {cᵀx : x ∈ ℝ^q, Ax ≤ b}` that has an optimal solution, `f (A, b, c)` is a list of `q`
rationals forming an optimal solution.

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with input encoding
`encLP` and output encoding `encListRat`; the machine halts in polynomial time on every input, and
its output is constrained only when an optimal solution exists. The LP is posed over `ℝ^q` with the
data cast from `ℚ`; optimality is `IsMinimizer`. The entry `j` of the output is `(f L).getD j 0`. -/
theorem lp_polytime :
    ∃ f : LPInst → List ℚ,
      Nonempty (Turing.TM2ComputableInPolyTime encLP encListRat f) ∧
      ∀ L : LPInst,
        (∃ x : Fin L.q → ℝ, IsMinimizer (fun j => (L.c j : ℝ))
          (polyhedron (L.A.map (Rat.cast : ℚ → ℝ)) (fun i => (L.b i : ℝ))) x) →
        (f L).length = L.q ∧
          IsMinimizer (fun j => (L.c j : ℝ))
            (polyhedron (L.A.map (Rat.cast : ℚ → ℝ)) (fun i => (L.b i : ℝ)))
            (fun j : Fin L.q => (((f L).getD j 0 : ℚ) : ℝ)) := by sorry

end RobustToDynamics
