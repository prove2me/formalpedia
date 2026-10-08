-- Prove2me | Theorems.Thm_RunwayCPS_Makespan_pruned_paths
-- name    : RunwayCPS.Makespan.pruned_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:52.595454+00:00
-- url     : https://prove2.me/theorems/afdc83cf-5119-43b8-8890-b759a46333b2
-- title:
--   §3.1 — the pruned network's source-sink paths are exactly the k-CPS sequences respecting precedence
-- statement:
--   Consider a runway instance with maximum shift $k$ and a finite set of precedence pairs $(x,y)$ ("$x$ lands before $y$") with $x\ne y$. Let $G$ be the pruned network: the CPS network without the nodes that violate some precedence pair, where a node violates $(x,y)$ if $y$ appears in it before $x$, or it has $y$ at a position less than $x-k$, or $x$ at a position greater than $y+k$.
--
--   For every map $\sigma$ from positions to aircraft,
--
--   $$\big(\sigma \text{ is } k\text{-CPS and respects every precedence pair}\big)\iff \sigma \text{ is the sequence of some source-sink path of } G.$$
--
--   This is the paper's conclusion from Lemmas 1 and 2 that removing violating nodes "is not only necessary but also sufficient for eliminating all source-sink paths that violate precedence constraints", and it is what lets the dynamic program of §4 handle precedence constraints by running on $G$.
--
--   **Formalization Note** Aircraft and positions are 0-based, stages 1-based. Pairs $(x,x)$ are excluded, as the paper's pairs are of two aircraft $a<b$; one finite set of ordered pairs covers both of the paper's cases.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1654, §3.1, paragraph after Lemma 1 and the Case II procedure after Lemma 2

import Mathlib
import Definitions.Def_RunwayCPS_Makespan_Network

namespace RunwayCPS.Makespan

/-- §3.1, conclusion after Lemma 1 and the Case II procedure (p. 1654): removing the nodes that
violate a precedence pair (after the Case II position filter) eliminates exactly the
source-sink paths that violate precedence. A sequence `σ` is a `k`-CPS sequence respecting
every precedence pair if and only if it is the sequence of a source-sink path of the pruned
network `G`. -/
theorem pruned_paths {n : ℕ} [NeZero n] (I : Instance n)
    (hprec : ∀ xy ∈ I.prec, xy.1 ≠ xy.2) (σ : Fin n → Fin n) :
    (IsCPS I.k σ ∧ RespectsPrec I.prec σ) ↔
      ∃ v : ℕ → List (Fin n), IsPathIn n (IsGNode I) I.k v ∧ pathSeq v = σ := by sorry

end RunwayCPS.Makespan
