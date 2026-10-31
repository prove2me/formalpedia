-- Prove2me | Theorems.Thm_StreamSubmod_theorem_1
-- name    : StreamSubmod.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:31.084295+00:00
-- url     : https://prove2.me/theorems/c86a115b-4c9a-48f2-b6ca-f587b7275dfb
-- title:
--   Theorem 1: StreamProcess is an $(\alpha/(1+\alpha)-\varepsilon)$-approximation (corrected: $\log\alpha^{-1}$ read as $1+\log\alpha^{-1}$, $\log(k/\alpha)$ as $1+\log(k/\alpha)$)
-- statement:
--   Let OfflineAlg be an $\alpha$-approximation offline algorithm for maximizing a non-negative submodular function subject to a cardinality constraint, and let $\varepsilon\in(0,1]$. StreamProcess, that is Algorithm 2 with $p=\lceil4/\varepsilon\rceil$ and $\varepsilon'=\varepsilon/2$, is a single-pass algorithm with the following properties, for every ground set, every non-negative submodular $f$, every $k\ge1$ and every arrival order, with one universal constant $C$:
--
--   1. the output $S$ satisfies $|S|\le k$ for every seed of OfflineAlg;
--   2. its expected value satisfies
--   $$
--   \mathbb E[f(S)]\ \ge\ \Bigl(\frac{\alpha}{1+\alpha}-\varepsilon\Bigr)f(\mathrm{OPT});
--   $$
--   3. after every prefix of the stream it stores at most $C\,k\,\varepsilon^{-2}(1+\log\alpha^{-1})$ elements;
--   4. it makes at most $C\,\varepsilon^{-2}(1+\log(k/\alpha))$ value computations while processing each arriving element;
--   5. every call of OfflineAlg receives a ground set of at most $pk$ elements;
--   6. if OfflineAlg is deterministic, then so is the algorithm: its output does not depend on the seed.
--
--   With exact post-processing, $\alpha=1$, the ratio is $1/2-\varepsilon$, which is the best possible ratio for a streaming algorithm of small memory up to $\varepsilon$.
--
--   **Formalization Note** Clause 5 stands in for the "nearly linear space" of OfflineAlg, which only serves to make the whole procedure semi-streaming.
--
--   Differences from the source:
--   - correction: O(kε⁻² log α⁻¹) elements and O(ε⁻² log(k/α)) marginal value computations → the factors 1 + log α⁻¹ and 1 + log(k/α); reason: the literal bounds are 0 at α = 1 and k = 1, yet for V = {e}, f(S) = |S|, k = 1, α = 1, ε = 1/4 an algorithm storing nothing outputs ∅, worth 0 < 1/4; the proof itself gives log c⁻¹ ≥ log 2
--   - generalization: "there exists" an algorithm → the paper's own algorithm, with the parameters of the proof; reason: a statement about the witness implies the existence claim
--   - generalization: OfflineAlg has space complexity nearly linear in the size of the ground set → no space hypothesis on Off, and instead the clause that Off receives at most pk elements; reason: that hypothesis only makes the whole procedure semi-streaming, and the guarantee holds for every Off
--   - encoding: O(·) and "constant ε" → one universal constant C, chosen before E, f, k, α and ε; reason: this is the meaning of O(·) with all parameters shown
--   - encoding: "marginal value computations", with O(p) of them charged to line 4 → a count returned by the step function: 1 + p|T| evaluations for line 4 and one for each marginal of line 10; reason: line 4 is counted without caching, which has the same order, so the bound is at least as strong
--   - encoding: a "semi-streaming algorithm" → the left fold alg2Run, whose memory is m and the sets S^τ_i, with clauses 3 and 5; reason: m is one number, T is determined by m, and the clauses bound the elements in memory and those passed to OfflineAlg
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E, for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: "if there are multiple options for i, pick an arbitrary one" → the smallest admissible index i, the same rule in Algorithms 1 and 2; reason: the paper leaves the rule free, and Corollary 16 needs both algorithms to choose alike
--   - encoding: a possibly randomized OfflineAlg → a finite seed type Ω with a probability vector μ, and Off ω U is the output on U with seed ω; reason: outputs are subsets of a finite set, so every randomized algorithm has this form
--   - generalization: OfflineAlg is an α-approximation algorithm for every instance of the problem (every non-negative submodular function and cardinality bound) → IsApproxOffline f k α μ Off: the guarantee is assumed only for the given f and k, on every ground set U ⊆ V; reason: the algorithms call OfflineAlg only with this f and k, so an algorithm that is α-approximate on every instance satisfies the hypothesis
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k is undefined
--   - encoding: guesses τ ∈ T of the form (1+ε′)^h → the exponents h : ℤ of the guesses; reason: h ↦ (1+ε′)^h is injective for ε′ > 0
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Theorem 1, p.14 (first stated p.6; proof p.15)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm2

namespace StreamSubmod

open NonmonotoneSubmod.Shared in
/-- Theorem 1 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.14; first stated p.6; proof
p.15): given an `α`-approximation offline algorithm OfflineAlg for maximizing a non-negative
submodular function subject to a cardinality constraint, for every constant `ε ∈ (0, 1]` there is an
`(α/(1+α) - ε)`-approximation semi-streaming algorithm for this problem. It stores
`O(kε⁻² log α⁻¹)` elements and makes `O(ε⁻² log(k/α))` marginal value computations while processing each
arriving element. If OfflineAlg is deterministic, then so is the algorithm.

The algorithm is StreamProcess: Algorithm 2 with `p = ⌈4/ε⌉` and `ε' = ε/2` (proof, p.15).

**Formalization Note.** The constant `C` of the `O(·)` bounds is universal: it is chosen before the
ground set, `f`, `k`, `α` and `ε`. The factors are `1 + log α⁻¹` and `1 + log(k/α)`: the literal
`log α⁻¹` vanishes at `α = 1`, and no algorithm storing nothing can be a `(1/2 - ε)`-approximation. The
"nearly linear space" of OfflineAlg only serves to make the whole procedure semi-streaming; the
statement records instead that every call of OfflineAlg receives at most `pk` elements. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ (Ω : Type) [Fintype Ω] (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E),
      IsApproxOffline f k α μ Off →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ σ : List E, IsStream σ →
      let p := ⌈4 / ε⌉₊
      let ε' := ε / 2
      (∀ ω, (alg2Out p f k α ε' Off σ ω).card ≤ k) ∧
      (α / (1 + α) - ε) * optVal f k ≤ ∑ ω, μ ω * f (alg2Out p f k α ε' Off σ ω) ∧
      (∀ L, L <+: σ →
        (alg2Stored k α ε' (alg2Run p f k α ε' L) : ℝ) ≤
          C * (k : ℝ) * ε⁻¹ ^ 2 * (1 + Real.log α⁻¹)) ∧
      (∀ L e, L ++ [e] <+: σ →
        (alg2Queries p f k α ε' L e : ℝ) ≤ C * ε⁻¹ ^ 2 * (1 + Real.log ((k : ℝ) / α))) ∧
      (∀ h ∈ alg2Guesses k α ε' (alg2Run p f k α ε' σ),
        (Finset.univ.biUnion ((alg2Run p f k α ε' σ).sets h)).card ≤ p * k) ∧
      ((∀ ω ω' U, Off ω U = Off ω' U) →
        ∀ ω ω', alg2Out p f k α ε' Off σ ω = alg2Out p f k α ε' Off σ ω') := by sorry

end StreamSubmod
