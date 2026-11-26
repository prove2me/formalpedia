-- Prove2me | Theorems.Thm_StreamSubmod_Supplement_observation_21
-- name    : StreamSubmod.Supplement.observation_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:44:26.818082+00:00
-- url     : https://prove2.me/theorems/4555b6ff-f6fb-5bd2-9a4b-4a275a6561d0
-- title:
--   Observation 21: Algorithm 3 stores $O(k/p)$ elements
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $V$ be a finite ground set, $f:2^V\to\mathbb R_{\ge0}$ non-negative and submodular, $k\ge1$, $p\in(0,1)$, $c>0$ and $0\le\tau\le f(\mathrm{OPT})$. For every stream presenting each element of $V$ exactly once, and after every prefix $L$ of it (the empty one included), the fractional solution $x$ of Algorithm 3 satisfies
--
--   $$
--   |\operatorname{supp}(x)|\ \le\ C\cdot\frac{k}{p}.
--   $$
--
--   Since Algorithm 3 needs to store only the elements of $\operatorname{supp}(x)$, it stores $O(k/p)$ elements.
--
--   Differences from the source:
--   - encoding: O(·) → one universal constant C, chosen before the ground set, f, k and every parameter of the algorithm; reason: this is the meaning of O(·) with all parameters shown
--   - encoding: the number of elements Algorithm 3 stores → |supp(x)| for the fractional solution x after every prefix of the stream, the empty prefix included; reason: by the proof of Observation 21 (p.23), Algorithm 3 needs to store only the elements of supp(x)
--   - generalization: Appendix C assumes an estimate τ with (1 − ε/8)·f(OPT) ≤ τ ≤ f(OPT) (p.21) → 0 ≤ τ ≤ f(OPT); reason: the result does not involve ε, and since f ≥ 0 the section's window implies 0 ≤ τ ≤ f(OPT), so the Lean statement covers every τ the paper allows
--   - encoding: the elements of V arrive one at a time, in an arbitrary order → a duplicate-free list σ containing every element of E (IsStream), for every such list; reason: this is a single pass over V; no arrival order is excluded
--   - encoding: k is a cardinality bound, never stated to be positive → the hypothesis 1 ≤ k; reason: this excludes only k = 0, where the threshold cτ/k of Algorithm 3 is undefined
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Observation 21 and its proof, p.23

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_Supplement_Basic
import Definitions.Def_StreamSubmod_Supplement_Algorithm3

namespace StreamSubmod.Supplement

open NonmonotoneSubmod.Shared StreamSubmod in
/-- Observation 21 (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3, p.23): Algorithm 3 can
be implemented so that it stores at most `O(k/p)` elements. By the proof (p.23), it needs to store
only the elements of `supp(x)`.

**Formalization Note.** The stored elements after a prefix `L` of the stream are those of
`supp(x)` for the current fractional solution `x = alg3Run f k p c τ L`; the empty prefix is
included. The constant `C` of `O(·)` is universal: it is chosen before the ground set, `f`, `k`,
`p`, `c` and `τ`. -/
theorem observation_21 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] (f : Finset E → ℝ), (∀ S, 0 ≤ f S) →
      Submodular f →
      ∀ k : ℕ, 1 ≤ k → ∀ p : ℝ, 0 < p → p < 1 → ∀ c : ℝ, 0 < c →
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ optVal f k →
      ∀ σ : List E, IsStream σ →
      ∀ L, L <+: σ → ((supp (alg3Run f k p c τ L)).card : ℝ) ≤ C * (k : ℝ) / p := by sorry

end StreamSubmod.Supplement
