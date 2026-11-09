-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_lemma_13
-- name    : TwoOptAllExp.TSP.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:22:42.022387+00:00
-- url     : https://prove2.me/theorems/c45f0c74-676e-4a6f-9b6d-98aec3396d7d
-- title:
--   Lemma 13 — improving sequences from $\tau_0$ follow $\hat P_n$
-- statement:
--   Let $n\ge1$, and let $\hat P_n$ be obtained from $P_n$ by deleting all occurrences of $E_i^4$.
--
--   1. $P_n$ is improving: applied from $\tau_0$ it is an improving swap sequence of $G_n$.
--
--   Let moreover a sequence of tours be an improving swap sequence of $G_n$ from $\tau_0$. Then each of its swaps carries a label, and for the list $L$ of labels:
--
--   2. the changes other than $E_i^4$ form a prefix of $\hat P_n$;
--   3. at the tour reached, every improving change is the next unperformed change of $\hat P_n$ or an occurrence of $E_i^4$ whose corresponding $D_i^0$ has occurred and which has not yet been performed; the next unperformed change is improving if it is applicable; and every such occurrence of $E_i^4$ is an improving change;
--   4. the next unperformed change is inapplicable only when it is $E_i^0$ and the corresponding $E_i^4$ has not been performed.
--
--   A change is applicable at a tour if some tour differing from it by a 2-swap realizes the change. The lemma says that the dynamics from $\tau_0$ is deterministic up to the moment at which the moves $E_i^4$ are performed.
--
--   Differences from the source:
--   - encoding: "at each reachable tour" → at the last tour of any improving swap sequence of $G_n$ from $\tau_0$; reason: this is what reachable means
--   - encoding: "corresponding $D_i^0$" → $E_i^4$ is pending when $L$ has fewer occurrences of $E_i^4$ than of $D_i^0$; reason: the $m$-th $E_i^4$ corresponds to the $m$-th $D_i^0$ in $P_n$
--   - reading: "the only improving changes are" the listed ones → every improving change is listed, and every listed change is improving (the next change if it is applicable); reason: the proof of (J_k) on p. 21 says "precisely when"; the stronger reading is taken
--   - reading: an instance $I_n$ for each $n\in\mathbb N$ (p. 13, with $0\in\mathbb N$) → $n\ge1$; reason: the construction has distinct layers $F_0$ and $F_n$, and Corollary 14 and the traversals $P_k$ start at $1$
--   - encoding: vertices of $G_n$ with the identified interfaces → the type `Vtx n` of named points, with $X_i$, $X_i''$, $X_i'$ abbreviations of $A_{i-1}'$, $A_{i-1}''$, $A_{i-1}$ and likewise for $Y$; reason: Lean convention; one vertex per identified class, $13n-3$ in total
--   - encoding: a tour as a Hamiltonian cycle → a tour as the edge set of a Hamiltonian cycle (`IsTourOf`); reason: Lean convention; the swaps of p. 7 act on edge sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 13, p. 21

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Canonical

namespace TwoOptAllExp.TSP

/-- **Lemma 13**, p. 21. `P_n` is improving from `τ₀`. In every improving swap sequence from `τ₀`,
with list of labels `L`, the changes other than `E_i^4` form a prefix of `P̂_n`. At the tour reached:
every improving change is the next unperformed change of `P̂_n` or a pending `E_i^4`; the next
unperformed change is improving if it is applicable; every pending `E_i^4` is an improving change;
and the next unperformed change is inapplicable only when it is `E_i^0` with the corresponding
`E_i^4` not performed. -/
theorem lemma_13 (n : ℕ) (hn : 1 ≤ n) :
    (∃ t : ℕ → (space n).Sol, (t 0).1 = tau0 n ∧ (space n).IsImprovingSeq (P n).length t ∧
      HasLabels n (P n).length t (P n)) ∧
    ∀ (ℓ : ℕ) (t : ℕ → (space n).Sol), (t 0).1 = tau0 n → (space n).IsImprovingSeq ℓ t →
      ∃ L : List Label, HasLabels n ℓ t L ∧
        (L.filter Label.isOrdinary) <+: hatP n ∧
        (∀ σ, (space n).IsImprovingMove (t ℓ) σ → ∃ l, Realizes n (t ℓ).1 σ.1 l ∧
          (nextChange n L = some l ∨ ∃ i, l = .E i 4 ∧ Pending L i)) ∧
        (∀ l σ, nextChange n L = some l → σ ∈ (space n).Nbr (t ℓ) →
          Realizes n (t ℓ).1 σ.1 l → (space n).IsImprovingMove (t ℓ) σ) ∧
        (∀ i, Pending L i → ∃ σ, (space n).IsImprovingMove (t ℓ) σ ∧
          Realizes n (t ℓ).1 σ.1 (.E i 4)) ∧
        (∀ l, nextChange n L = some l →
          (¬ ∃ σ ∈ (space n).Nbr (t ℓ), Realizes n (t ℓ).1 σ.1 l) →
            ∃ i, l = .E i 0 ∧ Pending L i) := by sorry

end TwoOptAllExp.TSP
