-- Prove2me | Theorems.Thm_StreamSubmod_observation_11
-- name    : StreamSubmod.observation_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:15.247363+00:00
-- url     : https://prove2.me/theorems/efc97546-8bb9-4b69-830d-33d6eec0b1f9
-- title:
--   Observation 11: $|S^\tau_i|\le mk/(c\tau)+1$
-- statement:
--   Let $f$ be non-negative and submodular and let $c=\alpha/(1+\alpha)$. At the end of every iteration of Algorithm 2, the size of the set $S^\tau_i$ satisfies
--
--   $$
--   |S^\tau_i|\ \le\ \frac{mk}{c\tau}+1
--   $$
--
--   for every $\tau\in T$ and integer $1\le i\le p$. Together with $|S^\tau_i|\le k$ this bounds the total space of Algorithm 2.
--
--   Differences from the source:
--   - generalization: at the end of every iteration → the state after every prefix of the stream, including the empty one; reason: the empty prefix adds only the initial state, whose sets are empty
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
--   - encoding: guesses τ ∈ T of the form (1+ε′)^h → the exponents h : ℤ of the guesses; reason: h ↦ (1+ε′)^h is injective for ε′ > 0
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Observation 11, p.12

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Algorithm2

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Observation 11 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.12): at the end of
every iteration of Algorithm 2, the size of the set `S^τ_i` is at most `mk/(cτ) + 1` for every
`τ ∈ T` and integer `1 ≤ i ≤ p`, where `c = α/(1+α)`.

**Formalization Note.** The end of an iteration is the memory after a prefix `L` of the stream. The
empty prefix is included. -/
theorem observation_11 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (ε' : ℝ) (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ) (hp : 1 ≤ p) (σ : List E)
    (hσ : IsStream σ) (L : List E) (hL : L <+: σ) :
    let st := alg2Run p f k α ε' L
    let c := α / (1 + α)
    ∀ h ∈ alg2Guesses k α ε' st, ∀ i,
      ((st.sets h i).card : ℝ) ≤ st.m * (k : ℝ) / (c * (1 + ε') ^ h) + 1 := by sorry

end StreamSubmod
