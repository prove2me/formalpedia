-- Prove2me | Theorems.Thm_QLLL_SAT_exists_assignment_forall
-- name    : QLLL.SAT.exists_assignment_forall
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:33.485992+00:00
-- url     : https://prove2.me/theorems/d136b0e9-30b1-47c3-b19c-6033c07270cc
-- title:
--   Infinite $k$-SAT: bounded variable occurrence implies a global satisfying assignment, at any cardinality
-- statement:
--   A clause is a disjunction of literals over boolean variables, and an assignment satisfies it if at least one literal evaluates to true. Let $\mathcal{V}$ be an arbitrary set of variables and let $(C_i)_{i \in I}$ be clauses over $\mathcal{V}$ indexed by an arbitrary set $I$; neither set needs to be finite or countable. Let $k \ge 1$ and $D \ge 1$ be integers such that:
--
--   1. every clause $C_i$ involves exactly $k$ distinct variables;
--   2. every variable occurs in at most $D$ clauses of every finite subfamily (equivalently, in at most $D$ clauses in total);
--   3. $D \cdot e \cdot k \le 2^{k}$.
--
--   Then there is a single assignment $a : \mathcal{V} \to \{0,1\}$ satisfying every clause $C_i$.
--
--   This extends Corollary 2 of Ambainis, Kempe and Sattath to infinite formulas. The conclusion is a single assignment because the space of all assignments is compact; the corresponding quantum statement for subspaces fails, since subspace lattices have no such compactness.
-- source:
--   Not in the paper; an infinite extension of Corollary 2. Formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Definitions.Def_QLLL_Classical_InfiniteKSAT
import Mathlib
import Std.Sat.CNF

open QLLL
open QLLL.SAT
open Finset Std.Sat

theorem QLLL.SAT.exists_assignment_forall {V ι : Type*} [DecidableEq V]
    (C : ι → CNF.Clause V) (k D : ℕ) (hk : 1 ≤ k) (hD1 : 1 ≤ D)
    (hvars : ∀ i, (clauseVars' (C i)).card = k)
    (hdeg : ∀ (v : V) (T : Finset ι),
      (T.filter fun i => v ∈ clauseVars' (C i)).card ≤ D)
    (hDk : (D : ℝ) * (Real.exp 1 * k) ≤ 2 ^ k) :
    ∃ a : V → Bool, ∀ i, CNF.Clause.eval a (C i) = true := by sorry
