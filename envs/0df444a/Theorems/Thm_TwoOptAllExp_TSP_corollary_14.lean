-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_corollary_14
-- name    : TwoOptAllExp.TSP.corollary_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:23:35.925204+00:00
-- url     : https://prove2.me/theorems/7f5ffc5a-6318-4836-a6c8-7eb4c4e8f9ab
-- title:
--   Corollary 14 — every maximal sequence is a rearrangement of $P_n$; length $3$ or $9\cdot2^{n-1}-7$
-- statement:
--   Let $n\ge1$. The canonical sequence $P_n$, applied from $\tau_0$, is a maximal improving swap sequence of $G_n$. Every maximal improving swap sequence of $G_n$ from $\tau_0$ is obtained from $P_n$ by moving occurrences of $E_i^4$ between their corresponding $D_i^0$ and $E_i^0$. All these sequences have length $3$ if $n=1$, and length
--   $$9\cdot2^{n-1}-7$$
--   if $n\ge2$.
--
--   Together with the bound on the instance size, this length gives the exponential lower bound of Theorem 1.
--
--   Differences from the source:
--   - encoding: "obtained from it by moving occurrences of $E_i^4$ between their corresponding $D_i^0$ and $E_i^0$" → the list of labels of the sequence is a rearrangement of $P_n$ (`IsRearrangement`); reason: the labels of a sequence record its swaps; `IsRearrangement` states the same ordinary subsequence and the same order within each triple
--   - reading: an instance $I_n$ for each $n\in\mathbb N$ (p. 13, with $0\in\mathbb N$) → $n\ge1$; reason: the construction has distinct layers $F_0$ and $F_n$, and Corollary 14 and the traversals $P_k$ start at $1$
--   - encoding: vertices of $G_n$ with the identified interfaces → the type `Vtx n` of named points, with $X_i$, $X_i''$, $X_i'$ abbreviations of $A_{i-1}'$, $A_{i-1}''$, $A_{i-1}$ and likewise for $Y$; reason: Lean convention; one vertex per identified class, $13n-3$ in total
--   - encoding: a tour as a Hamiltonian cycle → a tour as the edge set of a Hamiltonian cycle (`IsTourOf`); reason: Lean convention; the swaps of p. 7 act on edge sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Corollary 14, p. 24

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Canonical

namespace TwoOptAllExp.TSP

/-- **Corollary 14**, p. 24. The canonical sequence `P_n` is a maximal improving swap sequence from
`τ₀`, and every maximal improving swap sequence from `τ₀` has as list of labels a rearrangement of
`P_n`. All these sequences have length `3` if `n = 1` and `9 · 2^(n-1) - 7` if `n ≥ 2`. -/
theorem corollary_14 (n : ℕ) (hn : 1 ≤ n) :
    (∃ t : ℕ → (space n).Sol, (t 0).1 = tau0 n ∧ (space n).IsMaximalSeq (P n).length t ∧
      HasLabels n (P n).length t (P n)) ∧
    ∀ (ℓ : ℕ) (t : ℕ → (space n).Sol), (t 0).1 = tau0 n → (space n).IsMaximalSeq ℓ t →
      (∃ L : List Label, HasLabels n ℓ t L ∧ IsRearrangement (P n) L) ∧
        (n = 1 → ℓ = 3) ∧ (2 ≤ n → ℓ = 9 * 2 ^ (n - 1) - 7) := by sorry

end TwoOptAllExp.TSP
