-- Prove2me | Theorems.Thm_StreamSubmod_corollary_7
-- name    : StreamSubmod.corollary_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:48.046789+00:00
-- url     : https://prove2.me/theorems/4aab0930-9945-471d-8b4b-ccfa1c70e969
-- title:
--   Corollary 7: if no solution fills up, the output is worth at least $(\alpha/(\alpha+1)-2p^{-1})\tau$
-- statement:
--   Let $f$ be non-negative and submodular and let $0\le\tau\le f(\mathrm{OPT})$. If $|\hat S_i|<k$ for every integer $1\le i\le p$, then the output of Algorithm 1 has expected value at least
--
--   $$
--   \Bigl(\frac{\alpha}{\alpha+1}-2p^{-1}\Bigr)\tau.
--   $$
--
--   This is the bound independent of $b$, for the case that Lemma 3 does not cover.
--
--   Differences from the source:
--   - reading: the output "has value of at least" → the expected value of the output over the seed of the offline algorithm; reason: the output is random when OfflineAlg is, the proof bounds E[f(S_o)], and Proposition 8 says "expected value"
--   - generalization: the standing assumption (1−ε/2)·f(OPT) ≤ τ ≤ f(OPT) of §3 → 0 ≤ τ ≤ f(OPT); reason: the standing assumption implies this, since ε ≤ 1 and f ≥ 0, and the proof uses nothing more
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ, and Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem (every non-negative submodular function and cardinality bound) → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: the algorithms call OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Corollary 7, p.9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Corollary 7 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.9): if `|Ŝᵢ| < k` for
every `1 ≤ i ≤ p`, then the output of Algorithm 1 has value at least `(α/(α+1) - 2p⁻¹)τ`.

**Formalization Note.** "Value" is the expected value over the seed of the offline algorithm, as in
Proposition 8. The only condition on the estimate is `0 ≤ τ ≤ f(OPT)`. -/
theorem corollary_7 {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (p : ℕ) (hp : 1 ≤ p) (τ : ℝ) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ optVal f k) (σ : List E) (hσ : IsStream σ)
    (hlt : ∀ i, (alg1Sets p f k α τ σ i).card < k) :
    (α / (α + 1) - 2 * (p : ℝ)⁻¹) * τ ≤ ∑ ω, μ ω * f (alg1Out p f k α τ Off σ ω) := by sorry

end StreamSubmod
