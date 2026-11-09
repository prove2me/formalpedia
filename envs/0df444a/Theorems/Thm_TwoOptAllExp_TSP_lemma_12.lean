-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_lemma_12
-- name    : TwoOptAllExp.TSP.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:48.209197+00:00
-- url     : https://prove2.me/theorems/50afa3dc-911a-4db8-84a7-e12fc1ecee02
-- title:
--   Lemma 12 (Table 5) — all improving changes of states
-- statement:
--   Let $n\ge1$, and let $\tau,\sigma$ be tours of $G_n$ such that $\sigma$ is obtained from $\tau$ by a 2-swap and their states differ exactly in the state $T$, with values $r$ in $\tau$ and $r'$ in $\sigma$. Then $\sigma$ has smaller weight than $\tau$ if and only if the change of $T$ from $r$ to $r'$ is listed in Table 5:
--
--   | Item | Improving changes | Conditions |
--   |---|---|---|
--   | (a1) | $A_{n-1}:0\to1$ | none |
--   | (a2) | $A_i:0\to1$, $i<n-1$ | $(A_{i+1},D_{i+1})\in\{(0,2),(1,0)\}$ |
--   | (a3) | $A_i:1\to0$, $i<n-1$ | $(A_{i+1},D_{i+1})\in\{(0,0),(0,1),(1,1)\}$ |
--   | (b1) | $B_0:0\to1$ | $C_0=1$ |
--   | (b2) | $B_0:1\to0$ | $C_0=0$ |
--   | (b3) | $B_i:0\to1$, $i\ge1$ | $E_i=2$ |
--   | (b4) | $B_i:1\to0$, $i\ge1$ | $E_i\in\{0,1\}$ |
--   | (c1) | $C_0:0\to1$ | $A_0=1$ |
--   | (c2) | $C_0:1\to0$ | $A_0=0$ |
--   | (d1) | $D_i:1\to2\to0$ | $A_i=0$ |
--   | (d2) | $D_i:0\to1$ | $A_i=1$ |
--   | (e1) | $E_i:1\to2\to0$ | $(B_{i-1},B_i)=(0,0)$ |
--   | (e2) | $E_i:1\to3\to4\to0\to2$ | $(B_{i-1},B_i)=(0,1)$ |
--   | (e3) | $E_i:0\to1$ | $(B_{i-1},B_i)=(1,0)$ |
--   | (e4) | $E_i:0\to1\to2\to3\to4$ | $(B_{i-1},B_i)=(1,1)$ |
--
--   A row with a chain lists the change from every earlier value to every later value. The conditions refer to the states of $\tau$ other than $T$, which are also those of $\sigma$.
--
--   This table is the whole local dynamics of the construction.
--
--   Differences from the source:
--   - encoding: "all the improving changes of all states are exactly as stated in Table 5, subject to the validity conditions" → for two tours of $G_n$ differing by a 2-swap and exactly in one state, the move is improving if and only if the change is a row of Table 5; reason: both tours being tours is the validity condition by Lemma 11; "exactly" gives both directions
--   - reading: an instance $I_n$ for each $n\in\mathbb N$ (p. 13, with $0\in\mathbb N$) → $n\ge1$; reason: the construction has distinct layers $F_0$ and $F_n$, and Corollary 14 and the traversals $P_k$ start at $1$
--   - encoding: vertices of $G_n$ with the identified interfaces → the type `Vtx n` of named points, with $X_i$, $X_i''$, $X_i'$ abbreviations of $A_{i-1}'$, $A_{i-1}''$, $A_{i-1}$ and likewise for $Y$; reason: Lean convention; one vertex per identified class, $13n-3$ in total
--   - encoding: a tour as a Hamiltonian cycle → a tour as the edge set of a Hamiltonian cycle (`IsTourOf`); reason: Lean convention; the swaps of p. 7 act on edge sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 12 and Table 5, p. 19

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_States

namespace TwoOptAllExp.TSP

/-- **Lemma 12**, p. 19: for tours `τ`, `σ` of `G_n` that differ by a 2-swap and whose states differ
exactly in the state `v`, the move from `τ` to `σ` is improving if and only if the change of `v` is
listed in Table 5. -/
theorem lemma_12 (n : ℕ) (hn : 1 ≤ n) (τ σ : (space n).Sol) (hσ : σ ∈ (space n).Nbr τ) (v : Var)
    (hv : statesOf n τ.1 v ≠ statesOf n σ.1 v)
    (hw : ∀ w, w ≠ v → statesOf n τ.1 w = statesOf n σ.1 w) :
    (space n).IsImprovingMove τ σ ↔
      Table5 n (statesOf n τ.1) v (statesOf n τ.1 v) (statesOf n σ.1 v) := by sorry

end TwoOptAllExp.TSP
