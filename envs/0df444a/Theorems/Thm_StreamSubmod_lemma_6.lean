-- Prove2me | Theorems.Thm_StreamSubmod_lemma_6
-- name    : StreamSubmod.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:56.594438+00:00
-- url     : https://prove2.me/theorems/8f1c3f53-fc52-404d-954a-3fb3471fc32d
-- title:
--   Lemma 6: the bound on $\mathbb E[f(S_o)]$
-- statement:
--   Let $f$ be non-negative and submodular, let $\hat S_1,\dots,\hat S_p$ be the final sets of Algorithm 1, and let $S_o$ be the output of the $\alpha$-approximation algorithm OfflineAlg on $\bigcup_{i=1}^p\hat S_i$. Let $\mathrm{OPT}$ be a feasible set with $f(\mathrm{OPT})\ge\tau\ge0$, and let $O=\mathrm{OPT}\setminus\bigcup_{i=1}^p\hat S_i$, $b=|O|/k$. If $|\hat S_i|<k$ for every integer $1\le i\le p$, then
--
--   $$
--   \mathbb E[f(S_o)]\ \ge\ \alpha b\tau\Bigl(1-p^{-1}-\frac{\alpha b}{1+\alpha}\Bigr)+\alpha(1-b)\,f(\mathrm{OPT}\setminus O).
--   $$
--
--   Together with Lemma 5 this gives Corollary 7.
--
--   Differences from the source:
--   - generalization: OPT is an optimal solution → OPT is any set with |OPT| ≤ k and τ ≤ f(OPT); reason: the proof uses only these two properties; an optimal solution has them
--   - generalization: the standing assumption (1−ε/2)·f(OPT) ≤ τ ≤ f(OPT) of §3 → 0 ≤ τ, with τ ≤ f(OPT) as above; reason: the standing assumption implies this, since ε ≤ 1 and f ≥ 0, and the proof uses nothing more
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ, and Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem (every non-negative submodular function and cardinality bound) → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: the algorithms call OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Lemma 6, p.9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Lemma 6 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.9): with
`O = OPT \ ⋃ᵢ Ŝᵢ` and `b = |O|/k`, if `|Ŝᵢ| < k` for every `1 ≤ i ≤ p`, then
`E[f(S_o)] ≥ αbτ(1 - p⁻¹ - αb/(1 + α)) + α(1 - b) · f(OPT \ O)`.

**Formalization Note.** `S_o` is the output of the offline algorithm on `⋃ᵢ Ŝᵢ`, and the expectation
is over its seed. `OPT` is any feasible set with `f(OPT) ≥ τ`, not necessarily an optimal one, and
`0 ≤ τ`. -/
theorem lemma_6 {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (p : ℕ) (hp : 1 ≤ p) (τ : ℝ) (hτ0 : 0 ≤ τ) (σ : List E)
    (hσ : IsStream σ) (OPT : Finset E) (hOPT : OPT.card ≤ k) (hτ : τ ≤ f OPT)
    (hlt : ∀ i, (alg1Sets p f k α τ σ i).card < k) :
    let S := alg1Sets p f k α τ σ
    let O := OPT \ Finset.univ.biUnion S
    let b : ℝ := (O.card : ℝ) / (k : ℝ)
    α * b * τ * (1 - (p : ℝ)⁻¹ - α * b / (1 + α)) + α * (1 - b) * f (OPT \ O) ≤
      ∑ ω, μ ω * f (Off ω (Finset.univ.biUnion S)) := by sorry

end StreamSubmod
