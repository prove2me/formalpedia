-- Prove2me | Theorems.Thm_StreamSubmod_lemma_3
-- name    : StreamSubmod.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:40.400432+00:00
-- url     : https://prove2.me/theorems/d63ca8e7-ac39-4534-bac3-3855e95ed21c
-- title:
--   Lemma 3: a full solution makes the output worth at least $\alpha\tau/(1+\alpha)$
-- statement:
--   Let $f$ be non-negative and submodular, and let $\hat S_1,\dots,\hat S_p$ be the final sets of Algorithm 1 on a stream, with estimate $\tau$. If $|\hat S_i|=k$ for some integer $1\le i\le p$, then the output of Algorithm 1 has value
--
--   $$
--   f(\text{output})\ \ge\ \frac{\alpha\tau}{1+\alpha}.
--   $$
--
--   This is the easy case of the analysis of Algorithm 1.
--
--   Differences from the source:
--   - generalization: the standing assumption (1−ε/2)·f(OPT) ≤ τ ≤ f(OPT) of §3 → any real τ; reason: the standing assumption implies this, since ε ≤ 1 and f ≥ 0, and the proof uses nothing more
--   - reading: the output "has value of at least" → the bound for every seed ω of the offline algorithm; reason: the proof bounds the value of Ŝi, which is at most that of the output for every outcome; this implies the expected form
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ, and Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem (every non-negative submodular function and cardinality bound) → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: the algorithms call OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 3, p.7

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Lemma 3 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.7): if `|Ŝᵢ| = k` for some
`1 ≤ i ≤ p`, then the output of Algorithm 1 has value at least `ατ/(1+α)`.

**Formalization Note.** Stated for every seed `ω` of the offline algorithm, and with no condition
on the estimate `τ`. -/
theorem lemma_3 {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (p : ℕ) (hp : 1 ≤ p) (τ : ℝ) (σ : List E)
    (hσ : IsStream σ) (hfull : ∃ i, (alg1Sets p f k α τ σ i).card = k) (ω : Ω) :
    α * τ / (1 + α) ≤ f (alg1Out p f k α τ Off σ ω) := by sorry

end StreamSubmod
