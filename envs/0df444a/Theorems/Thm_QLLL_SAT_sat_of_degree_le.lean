-- Prove2me | Theorems.Thm_QLLL_SAT_sat_of_degree_le
-- name    : QLLL.SAT.sat_of_degree_le
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:29.999581+00:00
-- url     : https://prove2.me/theorems/523bd1b6-31f7-4f91-b5c5-a18ce0e4c57a
-- title:
--   Lovász Local Lemma for $k$-SAT: bounded variable occurrence implies satisfiability
-- statement:
--   A clause is a disjunction of literals over boolean variables, and an assignment satisfies it if at least one literal evaluates to true. Let $\Phi$ be a CNF formula over the variables $x_1, \dots, x_V$ in which every clause involves exactly $k$ distinct variables, where $k \ge 1$. Let $D \ge 1$ be an integer such that every variable occurs in at most $D$ clauses of $\Phi$, and suppose
--   $$D \cdot e \cdot k \ \le\ 2^{k}.$$
--   Then $\Phi$ is satisfiable.
--
--   This is Corollary 2 of Ambainis, Kempe and Sattath: a $k$-CNF formula in which every variable appears in at most $2^k / (e \cdot k)$ clauses is satisfiable. It is the classical model for the $k$-QSAT corollary `QLLL.QSAT.satisfiable_of_degree_le`.
--
--   **Formalization Note** Formulas are `Std.Sat.CNF (Fin V)` from the Lean core library and satisfiability is `Std.Sat.CNF.Sat`. The paper's bound "at most $2^k/(e k)$ clauses" is written as $D e k \le 2^k$ for an integer $D$. The hypotheses $k \ge 1$ and $D \ge 1$ are explicit; with $k \ge 1$ the case $D = 0$ only covers the empty formula.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), Corollary 2

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Mathlib
import Std.Sat.CNF

open QLLL
open QLLL.SAT
open Finset Std.Sat
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
variable {V : ℕ}

theorem QLLL.SAT.sat_of_degree_le {V : ℕ} (f : CNF (Fin V)) (k D : ℕ) (hk : 1 ≤ k) (hD1 : 1 ≤ D)
    (hvars : ∀ i : Fin f.clauses.size, (clauseVars (f.clauses[i.1]'i.2)).card = k)
    (hdeg : ∀ v : Fin V, (univ.filter fun i : Fin f.clauses.size =>
        v ∈ clauseVars (f.clauses[i.1]'i.2)).card ≤ D)
    (hDk : (D : ℝ) * (Real.exp 1 * k) ≤ 2 ^ k) :
    ∃ a, CNF.Sat a f := by sorry
