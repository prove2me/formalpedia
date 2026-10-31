-- Prove2me | Theorems.Thm_StreamSubmod_lemma_5
-- name    : StreamSubmod.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:07.125983+00:00
-- url     : https://prove2.me/theorems/dadf199b-9f14-4f7f-a05e-65b9519f9be1
-- title:
--   Lemma 5: the average solution is nearly as good as $O\cup A$
-- statement:
--   Let $f$ be non-negative and submodular, let $\tau\ge0$, and let $\hat S_1,\dots,\hat S_p$ be the final sets of Algorithm 1. Let $O=\mathrm{OPT}\setminus\bigcup_{i=1}^p\hat S_i$ and $b=|O|/k$. If $|\hat S_i|<k$ for every integer $1\le i\le p$, then for every fixed set $A\subseteq V$,
--
--   $$
--   p^{-1}\sum_{i=1}^p f(\hat S_i\cup A)\ \ge\ (1-p^{-1})\,f(O\cup A)-\frac{\alpha b\tau}{1+\alpha}.
--   $$
--
--   With $A=\varnothing$ this bounds the average value of the solutions; with $A=\mathrm{OPT}\setminus O$ it is an input to Lemma 6.
--
--   Differences from the source:
--   - generalization: OPT is an optimal solution → OPT is an arbitrary subset of V; reason: the proof uses only that the elements of O were rejected
--   - generalization: the standing assumption (1−ε/2)·f(OPT) ≤ τ ≤ f(OPT) of §3 → 0 ≤ τ; reason: the standing assumption implies this, since ε ≤ 1 and f ≥ 0, and the proof uses nothing more
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 5, p.8

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Lemma 5 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.8): with
`O = OPT \ ⋃ᵢ Ŝᵢ` and `b = |O|/k`, if `|Ŝᵢ| < k` for every `1 ≤ i ≤ p`, then for every fixed set
`A ⊆ V`, `p⁻¹ · ∑ᵢ f(Ŝᵢ ∪ A) ≥ (1 - p⁻¹) · f(O ∪ A) - αbτ/(1 + α)`.

**Formalization Note.** `OPT` is an arbitrary set here, and the only condition on the estimate is
`0 ≤ τ`. -/
theorem lemma_5 {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (p : ℕ)
    (hp : 1 ≤ p) (τ : ℝ) (hτ : 0 ≤ τ) (σ : List E) (hσ : IsStream σ) (OPT : Finset E)
    (hlt : ∀ i, (alg1Sets p f k α τ σ i).card < k) (A : Finset E) :
    let S := alg1Sets p f k α τ σ
    let O := OPT \ Finset.univ.biUnion S
    let b : ℝ := (O.card : ℝ) / (k : ℝ)
    (1 - (p : ℝ)⁻¹) * f (O ∪ A) - α * b * τ / (1 + α) ≤ (p : ℝ)⁻¹ * ∑ i, f (S i ∪ A) := by sorry

end StreamSubmod
