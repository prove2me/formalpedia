-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_completion_restriction
-- name    : TwoOptAllExp.TSP.completion_restriction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:38.43254+00:00
-- url     : https://prove2.me/theorems/2a75f193-889d-4e14-a99d-45fa17dd4d38
-- title:
--   §4.1, p. 14 — improving sequences from $\tau_0$ in $G_n'$ stay in $G_n$
-- statement:
--   Let $n\ge1$, let $G_n$ be the graph of §4.1 and $G_n'$ its completion, whose added edges have weight $2M+1$ with $M$ the largest edge weight of $G_n$. Then:
--
--   1. the initial tour $\tau_0$ is a tour of $G_n$;
--   2. every improving 2-opt sequence in $G_n'$ starting from $\tau_0$ consists of tours of $G_n$ and is an improving sequence in $G_n$;
--   3. every improving sequence in $G_n$ is an improving 2-opt sequence in $G_n'$;
--   4. a tour of $G_n$ is a local optimum for the 2-swaps in $G_n$ if and only if it is a local optimum for the 2-opt neighborhood of $G_n'$.
--
--   This statement allows the rest of the analysis to take place in the sparse graph $G_n$.
--
--   Differences from the source:
--   - generalization: no improving 2-opt sequence from the initial tour uses an added edge, "and we may restrict our analysis from now on to $G_n$" → in addition the converse transfer of improving sequences and the equivalence of local optimality; reason: these make "restrict our analysis" precise; clause 2 is the claim of the source
--   - reading: an instance $I_n$ for each $n\in\mathbb N$ (p. 13, with $0\in\mathbb N$) → $n\ge1$; reason: the construction has distinct layers $F_0$ and $F_n$, and Corollary 14 and the traversals $P_k$ start at $1$
--   - encoding: vertices of $G_n$ with the identified interfaces → the type `Vtx n` of named points, with $X_i$, $X_i''$, $X_i'$ abbreviations of $A_{i-1}'$, $A_{i-1}''$, $A_{i-1}$ and likewise for $Y$; reason: Lean convention; one vertex per identified class, $13n-3$ in total
--   - encoding: a tour as a Hamiltonian cycle → a tour as the edge set of a Hamiltonian cycle (`IsTourOf`); reason: Lean convention; the swaps of p. 7 act on edge sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, §4.1, Initial tour, p. 14

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Construction

namespace TwoOptAllExp.TSP

/-- §4.1, p. 14: the initial tour is a tour of `G_n`; every improving 2-opt sequence in the complete
graph `G'_n` starting from the initial tour stays in `G_n`; conversely every improving sequence in
`G_n` is one in `G'_n`; and a tour of `G_n` is a local optimum in `G_n` exactly when it is one in
`G'_n`. -/
theorem completion_restriction (n : ℕ) (hn : 1 ≤ n) :
    IsTourOf (G n) (tau0 n) ∧
    (∀ (ℓ : ℕ) (t : ℕ → (completedSpace n).Sol),
      (t 0).1 = tau0 n → (completedSpace n).IsImprovingSeq ℓ t →
        ∃ t' : ℕ → (space n).Sol, (space n).IsImprovingSeq ℓ t' ∧
          ∀ j ≤ ℓ, (t' j).1 = (t j).1) ∧
    (∀ (ℓ : ℕ) (t : ℕ → (space n).Sol), (space n).IsImprovingSeq ℓ t →
      ∃ t' : ℕ → (completedSpace n).Sol, (completedSpace n).IsImprovingSeq ℓ t' ∧
        ∀ j ≤ ℓ, (t' j).1 = (t j).1) ∧
    (∀ (τ : (space n).Sol) (τ' : (completedSpace n).Sol), τ.1 = τ'.1 →
      ((space n).IsLocalOpt τ ↔ (completedSpace n).IsLocalOpt τ')) := by sorry

end TwoOptAllExp.TSP
