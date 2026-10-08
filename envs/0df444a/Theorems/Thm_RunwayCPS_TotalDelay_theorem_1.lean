-- Prove2me | Theorems.Thm_RunwayCPS_TotalDelay_theorem_1
-- name    : RunwayCPS.TotalDelay.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:44.172654+00:00
-- url     : https://prove2.me/theorems/592d4d25-badf-45bf-9734-8ea63ebda18b
-- title:
--   Theorem 1 with §3.1 — k-CPS sequences respecting precedence are exactly the source-sink paths of the pruned CPS network
-- statement:
--   Let an instance be given with $n$ aircraft, maximum position shift $k$ and a finite set of precedence pairs $(x,y)$ with $x\ne y$, and let $G$ be the precedence-pruned CPS network.
--
--   1. For every $k$-CPS sequence $\sigma$ that places $x$ before $y$ for every precedence pair $(x,y)$, there is a source-sink path in $G$ whose sequence is $\sigma$.
--   2. Conversely, the sequence of every source-sink path in $G$ is such a $k$-CPS sequence: it is a permutation of the $n$ aircraft, moves each aircraft at most $k$ positions, and respects every precedence pair.
--
--   In short, the map $v\mapsto$ (sequence of $v$) sends source-sink paths of $G$ into, and onto,
--   $$\{k\text{-CPS sequences respecting the precedence pairs}\}.$$
--   This is Theorem 1 of the paper together with Lemmas 1 and 2, which show that deleting the nodes violating a precedence pair (after the position filter of Case II) deletes exactly the paths that violate it.
--
--   The statement is the foundation of every algorithm in the paper: optimizing over schedules becomes optimizing over paths of a network with polynomially many nodes in $n$ for fixed $k$.
--
--   **Formalization Note** Positions and aircraft are 0-based `Fin n`, and stages 0-based. The paper's precedence pairs always consist of two distinct aircraft ("for two aircraft $a$ and $b$ such that $a<b$"), so $x\ne y$ is a hypothesis: a pair $(x,x)$ can never be satisfied, yet no node violates it. The network keeps nodes that are unreachable from the source or the sink; they lie on no source-sink path, so this does not affect the statement.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1652–1654, Theorem 1 with §3.1 (Lemma 1, Lemma 2 and the pruning procedures of Cases I and II)

import Mathlib
import Definitions.Def_RunwayCPS_TotalDelay_Network

namespace RunwayCPS.TotalDelay

theorem theorem_1 {n : ℕ} (I : Instance n)
    (hprec : ∀ x y : Fin n, (x, y) ∈ I.prec → x ≠ y) :
    (∀ σ : Equiv.Perm (Fin n), IsCPS I.k σ → RespectsPrec I.prec σ →
        ∃ v : ℕ → List (Fin n), IsPathIn I v ∧ pathSeq v = ⇑σ) ∧
    (∀ v : ℕ → List (Fin n), IsPathIn I v →
        ∃ σ : Equiv.Perm (Fin n), IsCPS I.k σ ∧ RespectsPrec I.prec σ ∧ pathSeq v = ⇑σ) := by sorry

end RunwayCPS.TotalDelay
