-- Prove2me | Theorems.Thm_StreamSubmod_theorem_9
-- name    : StreamSubmod.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:11.010706+00:00
-- url     : https://prove2.me/theorems/d6e18573-c82a-4e25-b3eb-ac520f06796a
-- title:
--   Theorem 9: Algorithm 1 with $p=\lceil4/\varepsilon\rceil$ is an $(\alpha/(1+\alpha)-\varepsilon)$-approximation
-- statement:
--   Let OfflineAlg be an $\alpha$-approximation offline algorithm, and let $\varepsilon\in(0,1]$. Algorithm 1 with $p=\lceil4/\varepsilon\rceil$ and an estimate $\tau$ obeying
--
--   $$
--   (1-\varepsilon/2)\cdot f(\mathrm{OPT})\le\tau\le f(\mathrm{OPT})
--   $$
--
--   returns a feasible set of expected value at least $\bigl(\frac{\alpha}{1+\alpha}-\varepsilon\bigr)f(\mathrm{OPT})$. It stores $O(k\varepsilon^{-1})$ elements and calculates $O(\varepsilon^{-1})$ marginal values while processing each arriving element. The constant of the $O(\cdot)$ bounds is universal.
--
--   This is the version of the main result for a known estimate of $f(\mathrm{OPT})$.
--
--   Differences from the source:
--   - generalization: "there exists" an algorithm → the paper's own algorithm, with the parameters of the proof; reason: a statement about the witness implies the existence claim
--   - generalization: OfflineAlg has space complexity nearly linear in the size of the ground set → no space hypothesis on Off; reason: that hypothesis only makes the whole procedure semi-streaming, and the guarantee holds for every Off
--   - encoding: O(·) and "constant ε" → one universal constant C, chosen before E, f, k, α and ε; reason: this is the meaning of O(·) with all parameters shown
--   - encoding: a "semi-streaming algorithm" → the left fold alg1Sets with the stated bounds on stored elements, for every prefix; reason: the bounds are what semi-streaming asks of the memory in elements
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ, and Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem (every non-negative submodular function and cardinality bound) → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: the algorithms call OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Theorem 9, p.10

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Theorem 9 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.10): given an
`α`-approximation offline algorithm, for every `ε ∈ (0, 1]` Algorithm 1 with `p = ⌈4/ε⌉` (proof,
p.10) and an estimate `τ` of `f(OPT)` obeying `(1 - ε/2) · f(OPT) ≤ τ ≤ f(OPT)` is an
`(α/(1+α) - ε)`-approximation, stores `O(kε⁻¹)` elements and calculates `O(ε⁻¹)` marginal values while
processing each arriving element.

**Formalization Note.** The constant `C` of the `O(·)` bounds is universal: it is chosen before the
ground set, `f`, `k`, `α` and `ε`. -/
theorem theorem_9 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ (Ω : Type) [Fintype Ω] (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E),
      IsApproxOffline f k α μ Off →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ τ : ℝ, (1 - ε / 2) * optVal f k ≤ τ → τ ≤ optVal f k →
      ∀ σ : List E, IsStream σ →
      let p := ⌈4 / ε⌉₊
      (∀ ω, (alg1Out p f k α τ Off σ ω).card ≤ k) ∧
      (α / (1 + α) - ε) * optVal f k ≤ ∑ ω, μ ω * f (alg1Out p f k α τ Off σ ω) ∧
      (∀ L, L <+: σ → (alg1Stored (alg1Sets p f k α τ L) : ℝ) ≤ C * (k : ℝ) * ε⁻¹) ∧
      (∀ L e, L ++ [e] <+: σ → (alg1Queries p f k α τ L e : ℝ) ≤ C * ε⁻¹) := by sorry

end StreamSubmod
