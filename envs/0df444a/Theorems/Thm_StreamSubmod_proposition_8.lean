-- Prove2me | Theorems.Thm_StreamSubmod_proposition_8
-- name    : StreamSubmod.proposition_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:05.989194+00:00
-- url     : https://prove2.me/theorems/dd0baeb9-601e-4c69-990a-127d3508d59a
-- title:
--   Proposition 8: space, update time and expected value of Algorithm 1
-- statement:
--   Let $f$ be non-negative and submodular and let $0\le\tau\le f(\mathrm{OPT})$. Then Algorithm 1:
--
--   1. stores at most $pk$ elements at every moment, that is $\sum_i|S_i|\le pk$ after every prefix of the stream;
--   2. makes at most $p$ marginal value calculations while processing each arriving element;
--   3. has an output of expected value at least $\bigl(\frac{\alpha}{\alpha+1}-2p^{-1}\bigr)\tau$.
--
--   The first two clauses are Observation 2 (p.7). The proposition summarizes the analysis of Algorithm 1.
--
--   Differences from the source:
--   - generalization: stores O(pk) elements → at most p·k stored elements after every prefix of the stream; reason: an explicit constant 1 implies O(pk)
--   - generalization: the standing assumption (1−ε/2)·f(OPT) ≤ τ ≤ f(OPT) of §3 → 0 ≤ τ ≤ f(OPT); reason: the standing assumption implies this, since ε ≤ 1 and f ≥ 0, and the proof uses nothing more
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ, and Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem (every non-negative submodular function and cardinality bound) → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: the algorithms call OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Proposition 8, p.10 (with Observation 2, p.7)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Proposition 8 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.10; its first two
clauses are Observation 2, p.7): Algorithm 1 stores `O(pk)` elements, makes at most `p` marginal
value calculations while processing each arriving element, and its output set has an expected value
of at least `(α/(α+1) - 2p⁻¹)τ`.

**Formalization Note.** The stored elements are bounded explicitly by `pk` after every prefix of the
stream. The only condition on the estimate is `0 ≤ τ ≤ f(OPT)`. -/
theorem proposition_8 {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (p : ℕ) (hp : 1 ≤ p) (τ : ℝ) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ optVal f k) (σ : List E) (hσ : IsStream σ) :
    (∀ L, L <+: σ → alg1Stored (alg1Sets p f k α τ L) ≤ p * k) ∧
    (∀ L e, L ++ [e] <+: σ → alg1Queries p f k α τ L e ≤ p) ∧
    (α / (α + 1) - 2 * (p : ℝ)⁻¹) * τ ≤ ∑ ω, μ ω * f (alg1Out p f k α τ Off σ ω) := by sorry

end StreamSubmod
