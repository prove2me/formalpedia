-- Prove2me | Theorems.Thm_StreamSubmod_lemma_10
-- name    : StreamSubmod.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:11.410389+00:00
-- url     : https://prove2.me/theorems/c455e67d-b78d-4210-b4ee-bff463b72560
-- title:
--   Lemma 10: $f(S^\tau_i)\ge\alpha\tau|S^\tau_i|/((1+\alpha)k)$ throughout Algorithm 2
-- statement:
--   Let $f$ be non-negative and submodular. At every point during the execution of Algorithm 2, for every $\tau\in T$ and $1\le i\le p$,
--
--   $$
--   f(S^\tau_i)\ \ge\ \frac{\alpha\tau\,|S^\tau_i|}{(1+\alpha)k}.
--   $$
--
--   This is the counterpart of Lemma 3 for a partial solution, and the first step towards bounding the space of Algorithm 2.
--
--   Differences from the source:
--   - reading: "at every point during the execution" → the state after every prefix of the stream, between two arrivals; reason: the sets change only inside an iteration, and the proof of Observation 11 uses the lemma at this point
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
--   - encoding: guesses τ ∈ T of the form (1+ε′)^h → the exponents h : ℤ of the guesses; reason: h ↦ (1+ε′)^h is injective for ε′ > 0
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 10, p.12

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Algorithm2

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Lemma 10 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.12): at every point during
the execution of Algorithm 2, for every `τ ∈ T` and `1 ≤ i ≤ p` it holds that
`f(S^τ_i) ≥ ατ·|S^τ_i|/((1+α)k)`.

**Formalization Note.** "Every point" is every state between two arrivals: the memory after each
prefix `L` of the stream. A guess is `τ = (1 + ε')^h` with `h` in `T`. -/
theorem lemma_10 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (ε' : ℝ)
    (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ) (hp : 1 ≤ p) (σ : List E) (hσ : IsStream σ) (L : List E)
    (hL : L <+: σ) :
    let st := alg2Run p f k α ε' L
    ∀ h ∈ alg2Guesses k α ε' st, ∀ i,
      α * (1 + ε') ^ h * ((st.sets h i).card : ℝ) / ((1 + α) * (k : ℝ)) ≤ f (st.sets h i) := by sorry

end StreamSubmod
