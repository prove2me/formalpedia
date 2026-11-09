-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_lemma_11
-- name    : TwoOptAllExp.TSP.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:22:32.37097+00:00
-- url     : https://prove2.me/theorems/855e4688-b4ce-4a46-9c7f-b41c77173618
-- title:
--   Lemma 11 — valid state assignments and 2-swaps as single state changes
-- statement:
--   Let $n\ge1$.
--
--   1. An assignment of states determines a tour of $G_n$ if and only if, for every $i\in[n-1]$: the pair $(D_i,E_i)$ is not among $(0,2),(1,0),(1,3),(2,1),(2,4)$; $D_i=2$ implies $A_i=0$; if $E_i=2$ then $(B_{i-1},B_i)\ne(1,0)$; and if $E_i\in\{3,4\}$ then $B_i=1$.
--   2. Every 2-swap between two distinct tours of $G_n$ changes exactly one state.
--   3. If two valid assignments differ in exactly one state, then the corresponding tours differ by a 2-swap, except when that state is $E_i$ and its two values are $0$ and $3$, or $1$ and $4$; in these exceptional cases they do not differ by a 2-swap.
--
--   The lemma turns the neighborhood structure of the tours into a graph on state assignments.
--
--   Differences from the source:
--   - reading: "the corresponding tours differ by a 2-swap, except when that state is $E_i$ and its two values are 0 and 3, or 1 and 4" → an if and only if: in the excepted cases the tours do not differ by a 2-swap; reason: the proof on pp. 18–19 shows that three edges are exchanged in these cases; the stronger reading is taken
--   - encoding: an assignment "determines a tour" → the edge set `tourOf n s`, built from the pairings of Figs. 5 and 6 and the fixed edges, is a tour of $G_n$; reason: Lean convention for the construction of p. 17
--   - reading: an instance $I_n$ for each $n\in\mathbb N$ (p. 13, with $0\in\mathbb N$) → $n\ge1$; reason: the construction has distinct layers $F_0$ and $F_n$, and Corollary 14 and the traversals $P_k$ start at $1$
--   - encoding: vertices of $G_n$ with the identified interfaces → the type `Vtx n` of named points, with $X_i$, $X_i''$, $X_i'$ abbreviations of $A_{i-1}'$, $A_{i-1}''$, $A_{i-1}$ and likewise for $Y$; reason: Lean convention; one vertex per identified class, $13n-3$ in total
--   - encoding: a tour as a Hamiltonian cycle → a tour as the edge set of a Hamiltonian cycle (`IsTourOf`); reason: Lean convention; the swaps of p. 7 act on edge sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 11, pp. 17–18

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_States

namespace TwoOptAllExp.TSP

/-- **Lemma 11**, pp. 17–18. An assignment of states determines a tour of `G_n` if and only if it
satisfies the four conditions (`ValidStates`). Every 2-swap between two distinct tours changes
exactly one state. Two valid assignments that differ in exactly one state determine tours that
differ by a 2-swap, except when that state is `E_i` and its two values are `0` and `3`, or `1` and
`4`. -/
theorem lemma_11 (n : ℕ) (hn : 1 ≤ n) :
    (∀ s : Var → ℕ, IsAssignment n s → (IsTourOf (G n) (tourOf n s) ↔ ValidStates n s)) ∧
    (∀ τ σ : Finset (Sym2 (Vtx n)), IsTourOf (G n) τ → IsTourOf (G n) σ → τ ≠ σ →
      IsKSwap 2 τ σ → ∃! v : Var, statesOf n τ v ≠ statesOf n σ v) ∧
    (∀ (s t : Var → ℕ) (v : Var), IsAssignment n s → IsAssignment n t →
      ValidStates n s → ValidStates n t → s v ≠ t v → (∀ w, w ≠ v → s w = t w) →
        (IsKSwap 2 (tourOf n s) (tourOf n t) ↔
          ¬ ∃ i, v = .E i ∧
            (s v, t v) ∈ ([(0, 3), (3, 0), (1, 4), (4, 1)] : List (ℕ × ℕ)))) := by sorry

end TwoOptAllExp.TSP
