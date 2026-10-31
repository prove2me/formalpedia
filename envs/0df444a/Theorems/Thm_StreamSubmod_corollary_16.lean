-- Prove2me | Theorems.Thm_StreamSubmod_corollary_16
-- name    : StreamSubmod.corollary_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:50.282131+00:00
-- url     : https://prove2.me/theorems/ee94f98d-7f54-4fb1-bc88-265e59cc42ef
-- title:
--   Corollary 16: Algorithm 2 is at least as good as Algorithm 1 with a good estimate
-- statement:
--   Let $f$ be non-negative and submodular, and let OfflineAlg be an $\alpha$-approximation offline algorithm. If, for some choice of $\alpha$ and $p$, the approximation ratio of Algorithm 1 is at least $\beta$ for every estimate with
--
--   $$
--   (1-\varepsilon')\cdot f(\mathrm{OPT})\le\tau\le f(\mathrm{OPT}),
--   $$
--
--   then the approximation ratio of Algorithm 2 is at least $\beta$ as well for this choice of $\alpha$ and $p$.
--
--   This removes the assumption that an estimate of $f(\mathrm{OPT})$ is known. The case $\hat T=\varnothing$ is included, without any bound on $\beta$.
--
--   Differences from the source:
--   - generalization: an approximation ratio, which quantifies over all instances → one instance (f, k, Off, σ): the guarantee is assumed and concluded on that instance; reason: applying this to every instance gives the statement of the page
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ, and Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem (every non-negative submodular function and cardinality bound) → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: the algorithms call OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Corollary 16, p.14

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1
import Definitions.Def_StreamSubmod_Algorithm2

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Corollary 16 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.14): if the approximation
ratio of Algorithm 1 is at least `β` when `(1 - ε') · f(OPT) ≤ τ ≤ f(OPT)`, for some choice of the
parameters `α` and `p`, then the approximation ratio of Algorithm 2 is at least `β` as well for this
choice of `α` and `p`.

**Formalization Note.** Stated for one instance: the guarantee is assumed and concluded for the
given `f`, `k`, offline algorithm and stream. Both algorithms use the same rule for choosing `i`
and the same seed `ω`. -/
theorem corollary_16 {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (ε' : ℝ) (hε0 : 0 < ε') (hε1 : ε' < 1) (p : ℕ)
    (hp : 1 ≤ p) (σ : List E) (hσ : IsStream σ) (β : ℝ)
    (hβ : ∀ τ : ℝ, (1 - ε') * optVal f k ≤ τ → τ ≤ optVal f k →
      β * optVal f k ≤ ∑ ω, μ ω * f (alg1Out p f k α τ Off σ ω)) :
    β * optVal f k ≤ ∑ ω, μ ω * f (alg2Out p f k α ε' Off σ ω) := by sorry

end StreamSubmod
