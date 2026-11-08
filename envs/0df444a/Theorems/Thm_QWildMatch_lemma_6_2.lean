-- Prove2me | Theorems.Thm_QWildMatch_lemma_6_2
-- name    : QWildMatch.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:15:30.900664+00:00
-- url     : https://prove2.me/theorems/0955d19c-c6f7-41ec-9a55-0ebb690a0de8
-- title:
--   Lemma 6.2 — bounded-error sparse enumeration of at most $q$ marks
-- statement:
--   There are absolute constants $C>0$ and $c$ such that for every universe size $M$, every $q$ and every $\eta\in(0,1)$ there is one quantum query algorithm making $Q$ queries, with
--
--   $$Q\le C\sqrt{M(q+1)}\,\bigl(1+\log(1/\eta)\bigr)\bigl(1+\log(M+2)\bigr)^c,$$
--
--   which for every marking $g:[M]\to\{0,1\}$ with at most $q$ marks outputs the complete set of marks with probability at least $1-\eta$. The cases of zero marks and of fewer than $q$ marks are included, as are $q=0$ and $M=0$.
--
--   This is the primitive that produces the defect list of a block; a single circuit serves every marking.
--
--   Differences from the source:
--   - generalization: text queries for a predicate computable with $O(1)$ text queries → queries to the XOR oracle of the predicate $g$ itself; reason: a predicate computed with $c'$ text queries gives such an oracle with $2c'$ text queries (compute, copy, uncompute), so this bound implies the printed one.
--   - reading: $\tilde O(\sqrt{M(q+1)}\log(1/\eta))$ → $C\sqrt{M(q+1)}(1+\log(1/\eta))(1+\log(M+2))^c$ with absolute $C,c$; reason: this pins $\tilde O$ before the instance, and the $1+$ is needed since $\log(1/\eta)\to0$ as $\eta\to1$ while listing a mark costs a query.
--   - encoding: the complete canonical list → the `Finset` of marked positions; reason: a `Finset` is canonical by construction and carries the same information.
--   - encoding: success probability $1-\eta$ → probability at least $1-\eta$; reason: the usual meaning of a success guarantee.
--   - encoding: a universe of size $M$ → the index type `Option (Fin M)`, with `none` answering $0$; reason: this keeps the state space nonempty at $M=0$ and makes a query skippable.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), Lemma 6.2, p.8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace QWildMatch

open QAlgorithms

/-- Lemma 6.2 (Bounded-error sparse enumeration), Zhao et al., STOC 2027 submission (file sha256
9e87a9dd…), p.8.

**Formalization Note** `Õ` is pinned: `C` and `c` are absolute and precede `M`, `q`, `η`, with the
factor `(1 + log(M + 2))^c` (natural logarithm). The `1 + log(1/η)` replaces the page's `log(1/η)`,
which tends to `0` as `η → 1` although listing even one mark costs a query. Queries go to the predicate's
own XOR oracle: a predicate computable with `c'` text queries gives such an oracle with `2c'` text queries
(compute, copy, uncompute), so this bound implies the page's. One circuit `A` serves every `g` ("uniform").
The list is the marked set, canonical as a `Finset`. `card ≤ q` covers zero marks and fewer than `q`
marks; `q = 0` and `M = 0` are allowed. -/
theorem lemma_6_2 :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧
    ∀ (M q : ℕ) (η : ℝ), 0 < η → η < 1 →
    ∃ (N Q : ℕ) (A : QueryAlg (Option (Fin M)) (ZMod 2) (Qubits N) Q)
      (out : ((Option (Fin M) × ZMod 2) × Qubits N) → Finset (Fin M)),
      (Q : ℝ) ≤ C * √((M : ℝ) * ((q : ℝ) + 1)) * (1 + Real.log (1 / η)) *
        (1 + Real.log ((M : ℝ) + 2)) ^ c ∧
      ∀ g : Fin M → ZMod 2, (Finset.univ.filter (fun x => g x = 1)).card ≤ q →
        1 - η ≤ probEvent
          (A.finalState (xorOracle (fun i : Option (Fin M) => i.elim 0 g)))
          (fun z => out z = Finset.univ.filter (fun x => g x = 1)) := by sorry

end QWildMatch
