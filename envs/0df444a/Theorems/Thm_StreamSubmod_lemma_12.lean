-- Prove2me | Theorems.Thm_StreamSubmod_lemma_12
-- name    : StreamSubmod.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:16.15328+00:00
-- url     : https://prove2.me/theorems/c1a71ad3-b9d2-4a6b-839d-ba866b929b1a
-- title:
--   Lemma 12: space and update time of Algorithm 2 (corrected: $\log\alpha^{-1}$ read as $1+\log\alpha^{-1}$, $\log(k/\alpha)$ as $1+\log(k/\alpha)$)
-- statement:
--   Let $f$ be non-negative and submodular. Algorithm 2 can be implemented so that, for a universal constant $C$, for all $p\ge1$, $k\ge1$, $\alpha\in(0,1]$ and $\varepsilon'\in(0,1)$, after every prefix of the stream it stores at most
--
--   $$
--   C\,p\,k\,(\varepsilon')^{-1}\,(1+\log\alpha^{-1})
--   $$
--
--   elements, and it makes at most
--
--   $$
--   C\,p\,(\varepsilon')^{-1}\,\bigl(1+\log(k/\alpha)\bigr)
--   $$
--
--   value computations when processing each arriving element.
--
--   This gives the space and update-time clauses of Theorem 1.
--
--   Differences from the source:
--   - correction: O(pk(ε′)⁻¹ log α⁻¹) elements and O(p(ε′)⁻¹ log(k/α)) marginal value calculations → the factors 1 + log α⁻¹ and 1 + log(k/α); reason: the literal bounds are 0 at α = 1 and k = 1, yet for V = {e}, f(S) = |S|, k = 1, α = 1, p = 16, ε′ = 1/8 Algorithm 2 stores e and computes a marginal; the proof itself gives log c⁻¹ ≥ log 2
--   - reading: "can be implemented so that" → the implementation alg2Step, with stored elements and computations counted on it; reason: a statement about one implementation is what the sentence asks for
--   - encoding: O(·) and "constant ε" → one universal constant C, chosen before E, f, k, α and ε; reason: this is the meaning of O(·) with all parameters shown
--   - encoding: "marginal value computations", with O(p) of them charged to line 4 → a count returned by the step function: 1 + p|T| evaluations for line 4 and one for each marginal of line 10; reason: line 4 is counted without caching, which has the same order, so the bound is at least as strong
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
--   - encoding: guesses τ ∈ T of the form (1+ε′)^h → the exponents h : ℤ of the guesses; reason: h ↦ (1+ε′)^h is injective for ε′ > 0
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 12, p.12 (proof pp.12–13)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Algorithm2

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Lemma 12 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.12, proof pp.12–13):
Algorithm 2 can be implemented so that it stores `O(pk(ε')⁻¹ log α⁻¹)` elements and makes only
`O(p(ε')⁻¹ log(k/α))` marginal value calculations when processing each arriving element.

**Formalization Note.** The implementation is `alg2Step`. The constant `C` is universal: it is chosen
before all the parameters. The factors are `1 + log α⁻¹` and `1 + log(k/α)`: the literal `log α⁻¹`
vanishes at `α = 1` and `log(k/α)` at `k = 1, α = 1`, although the algorithm stores elements there. -/
theorem lemma_12 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ ε' : ℝ, 0 < ε' → ε' < 1 →
      ∀ p : ℕ, 1 ≤ p →
      ∀ σ : List E, IsStream σ →
      (∀ L, L <+: σ →
        (alg2Stored k α ε' (alg2Run p f k α ε' L) : ℝ) ≤
          C * (p : ℝ) * (k : ℝ) * ε'⁻¹ * (1 + Real.log α⁻¹)) ∧
      (∀ L e, L ++ [e] <+: σ →
        (alg2Queries p f k α ε' L e : ℝ) ≤
          C * (p : ℝ) * ε'⁻¹ * (1 + Real.log ((k : ℝ) / α))) := by sorry

end StreamSubmod
