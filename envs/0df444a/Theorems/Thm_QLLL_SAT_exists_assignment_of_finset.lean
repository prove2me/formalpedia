-- Prove2me | Theorems.Thm_QLLL_SAT_exists_assignment_of_finset
-- name    : QLLL.SAT.exists_assignment_of_finset
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:47.807121+00:00
-- url     : https://prove2.me/theorems/d3d09607-1211-4c2b-828c-7ad3b29105da
-- title:
--   $k$-SAT under bounded variable occurrence for a finite subfamily of clauses over arbitrary variable and index sets
-- statement:
--   A clause is a disjunction of literals over boolean variables, and an assignment satisfies it if at least one literal evaluates to true. Let $\mathcal{V}$ be an arbitrary set of variables and let $(C_i)_{i \in I}$ be clauses over $\mathcal{V}$ indexed by an arbitrary set $I$. Let $T \subseteq I$ be finite, and let $k \ge 1$ and $D \ge 1$ be integers such that:
--
--   1. every clause $C_i$ with $i \in T$ involves exactly $k$ distinct variables;
--   2. every variable occurs in at most $D$ of the clauses $C_i$ with $i \in T$;
--   3. $D \cdot e \cdot k \le 2^{k}$.
--
--   Then there is an assignment $a : \mathcal{V} \to \{0,1\}$ satisfying every $C_i$ with $i \in T$.
--
--   This transports Corollary 2 of Ambainis, Kempe and Sattath to arbitrary variable and index types, with hypotheses required only on $T$. It is the finite step in the compactness proof of the infinite version `QLLL.SAT.exists_assignment_forall`.
-- source:
--   Not in the paper; a transport of Corollary 2 to arbitrary variable and index types. Formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Definitions.Def_QLLL_Classical_InfiniteKSAT
import Mathlib
import Std.Sat.CNF

open QLLL
open QLLL.SAT
open Finset Std.Sat

theorem QLLL.SAT.exists_assignment_of_finset {V ι : Type*} [DecidableEq V]
    (C : ι → CNF.Clause V) (T : Finset ι) (k D : ℕ) (hk : 1 ≤ k) (hD1 : 1 ≤ D)
    (hvars : ∀ i ∈ T, (clauseVars' (C i)).card = k)
    (hdeg : ∀ v : V, (T.filter fun i => v ∈ clauseVars' (C i)).card ≤ D)
    (hDk : (D : ℝ) * (Real.exp 1 * k) ≤ 2 ^ k) :
    ∃ a : V → Bool, ∀ i ∈ T, CNF.Clause.eval a (C i) = true := by sorry
