-- Prove2me | Theorems.Thm_StreamSubmod_lemma_14
-- name    : StreamSubmod.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:24.163386+00:00
-- url     : https://prove2.me/theorems/c1c84545-649a-4261-af88-0269eda44a12
-- title:
--   Lemma 14: $\hat T$ contains $\hat\tau$ with $(1-\varepsilon^\prime)f(\mathrm{OPT})\le\hat\tau\le f(\mathrm{OPT})$
-- statement:
--   Let $f$ be non-negative and submodular, and let $\hat T$ be the final set of guesses of Algorithm 2, assumed non-empty as in the text preceding the lemma. Then $\hat T$ contains a value $\hat\tau$ such that
--
--   $$
--   (1-\varepsilon')\cdot f(\mathrm{OPT})\ \le\ \hat\tau\ \le\ f(\mathrm{OPT}).
--   $$
--
--   So Algorithm 2 runs at least one copy of Algorithm 1 with a good estimate.
--
--   Differences from the source:
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
--   - encoding: guesses τ ∈ T of the form (1+ε′)^h → the exponents h : ℤ of the guesses; reason: h ↦ (1+ε′)^h is injective for ε′ > 0
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 14, p.13

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Algorithm2

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Lemma 14 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.13): under the standing
assumption `T̂ ≠ ∅` of the text, the final set `T̂` of Algorithm 2 contains a value `τ̂` such that
`(1 - ε') · f(OPT) ≤ τ̂ ≤ f(OPT)`. -/
theorem lemma_14 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (ε' : ℝ)
    (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ) (hp : 1 ≤ p) (σ : List E) (hσ : IsStream σ)
    (hT : (alg2Guesses k α ε' (alg2Run p f k α ε' σ)).Nonempty) :
    ∃ h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' σ),
      (1 - ε') * optVal f k ≤ (1 + ε') ^ h ∧ (1 + ε') ^ h ≤ optVal f k := by sorry

end StreamSubmod
