-- Prove2me | Theorems.Thm_StreamSubmod_lemma_15
-- name    : StreamSubmod.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:32.850401+00:00
-- url     : https://prove2.me/theorems/cdc4d784-b876-4f23-afb6-4ade171b27c3
-- title:
--   Lemma 15: Algorithm 1 with $\hat\tau$ has empty sets until $\hat\tau$ enters $T$
-- statement:
--   Let $f$ be non-negative and submodular, and let $\hat\tau$ belong to the final set $\hat T$ of Algorithm 2. Let $e_j$ be the element whose arrival made Algorithm 2 add $\hat\tau$ to $T$. Then all the sets $\hat S_1,\dots,\hat S_p$ maintained by Algorithm 1 with the estimate $\hat\tau$ are empty immediately prior to the arrival of $e_j$.
--
--   Hence Algorithm 2 loses nothing by starting the sets of $\hat\tau$ late: their final contents equal those of Algorithm 1.
--
--   **Formalization Note** The statement is that for every prefix $L$ of the stream after which $\hat\tau\notin T$, the sets of Algorithm 1 with estimate $\hat\tau$ are empty after $L$. The prefix $e_1,\dots,e_{j-1}$ of the paper is the longest such prefix. If $\hat\tau$ belongs to $T$ from the beginning, then $j=1$, the prefix is empty and the sets are empty by construction.
--
--   Differences from the source:
--   - generalization: τ̂ is the value given by Lemma 14 → every τ̂ in the final set T̂; reason: the proof uses only τ̂ ∈ T̂
--   - generalization: immediately prior to the arrival of e_j → after every prefix of the stream after which τ̂ is not in T; reason: the prefix e_1, …, e_{j−1} is the longest such prefix, and for j = 1 it is empty
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
--   - encoding: guesses τ ∈ T of the form (1+ε′)^h → the exponents h : ℤ of the guesses; reason: h ↦ (1+ε′)^h is injective for ε′ > 0
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 15, p.14

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1
import Definitions.Def_StreamSubmod_Algorithm2

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Lemma 15 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.14): let `τ̂` belong to the
final set `T̂` of Algorithm 2, and let `e_j` be the element whose arrival made Algorithm 2 add `τ̂` to
`T`. Then all the sets `Ŝ_1, …, Ŝ_p` maintained by Algorithm 1 with the estimate `τ̂` are empty
immediately prior to the arrival of `e_j`.

**Formalization Note.** The prefix `e_1, …, e_{j-1}` is any prefix `L` of the stream after which `τ̂`
is not in `T`; the last such prefix is the one of the paper, and when `τ̂` belongs to `T` from the
beginning (`j = 1`) the prefix is empty, so the sets are empty by construction. -/
theorem lemma_15 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (ε' : ℝ)
    (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ) (hp : 1 ≤ p) (σ : List E) (hσ : IsStream σ) (h : ℤ)
    (hT : h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' σ)) (L : List E) (hL : L <+: σ)
    (hnot : h ∉ alg2Guesses k α ε' (alg2Run p f k α ε' L)) (i : Fin p) :
    alg1Sets p f k α ((1 + ε') ^ h) L i = ∅ := by sorry

end StreamSubmod
