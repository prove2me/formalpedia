-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_states_determine_tour
-- name    : TwoOptAllExp.TSP.states_determine_tour
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:19:38.439535+00:00
-- url     : https://prove2.me/theorems/43475f2f-c0c1-434a-9151-5473a8432c6c
-- title:
--   §4.3, p. 17 — states and tours determine each other; all states of $\tau_0$ are $0$
-- statement:
--   Let $n\ge1$. For every tour $H$ of $G_n$, the states of Definition 10 are well defined and form an assignment, and the edge set determined by this assignment is $H$. For every valid assignment $s$, the states of the edge set determined by $s$ are $s$. All states of $\tau_0$ are $0$.
--
--   So tours of $G_n$ and valid assignments may be identified, which is how Lemmas 11–13 are used.
--
--   Differences from the source:
--   - generalization: the states and the fixed edges "determine every edge of a reachable tour" → this for every tour of $G_n$, and also that a valid assignment is recovered from its edge set; reason: reachable tours are tours of $G_n$, so the claim of the source is a special case
--   - reading: an instance $I_n$ for each $n\in\mathbb N$ (p. 13, with $0\in\mathbb N$) → $n\ge1$; reason: the construction has distinct layers $F_0$ and $F_n$, and Corollary 14 and the traversals $P_k$ start at $1$
--   - encoding: vertices of $G_n$ with the identified interfaces → the type `Vtx n` of named points, with $X_i$, $X_i''$, $X_i'$ abbreviations of $A_{i-1}'$, $A_{i-1}''$, $A_{i-1}$ and likewise for $Y$; reason: Lean convention; one vertex per identified class, $13n-3$ in total
--   - encoding: a tour as a Hamiltonian cycle → a tour as the edge set of a Hamiltonian cycle (`IsTourOf`); reason: Lean convention; the swaps of p. 7 act on edge sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, §4.3, after Definition 10, p. 17

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_States

namespace TwoOptAllExp.TSP

/-- §4.3, p. 17: the states of a tour of `G_n` form an assignment that determines every edge of the
tour; a valid assignment is the assignment of states of the edge set it determines; and all states
of `τ₀` are `0`. -/
theorem states_determine_tour (n : ℕ) (hn : 1 ≤ n) :
    (∀ H : Finset (Sym2 (Vtx n)), IsTourOf (G n) H →
      IsAssignment n (statesOf n H) ∧ tourOf n (statesOf n H) = H) ∧
    (∀ s : Var → ℕ, IsAssignment n s → ValidStates n s → statesOf n (tourOf n s) = s) ∧
    (∀ v : Var, statesOf n (tau0 n) v = 0) := by sorry

end TwoOptAllExp.TSP
