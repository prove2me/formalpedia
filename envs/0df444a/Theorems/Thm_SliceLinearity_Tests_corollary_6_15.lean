-- Prove2me | Theorems.Thm_SliceLinearity_Tests_corollary_6_15
-- name    : SliceLinearity.Tests.corollary_6_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:40:51.849676+00:00
-- url     : https://prove2.me/theorems/0d562397-42a4-4a5c-9096-b8fe5df863a0
-- title:
--   Corollary 6.15 — case (i) of the goal: the conditioned symmetric active-set test on S(pn) with 1 + ⌈1/p⌉ queries
-- statement:
--   Fix $0<p\le1/2$, and set $k=1+\lceil1/p\rceil$. For all sufficiently large $n$ with $pn$ even, the symmetric active-set test with $k$ queries, conditioned on all queries lying in $S(pn)$, is perfectly complete, and also complete for affine maps when $k$ is even. If $f:S(pn)\to\{\pm1\}$ passes it with probability at least $(1+\delta)/2$, then, uniformly in $f$ and $\delta$,
--   $$\max_{\varphi\text{ affine}}\mathrm{agr}_\nu(f,\varphi)\ge\frac{1+\delta}2-o(1).$$
--
--   Differences from the source:
--   - reading: o(1) uniformly in f and δ → ε : ℕ → ℝ with ε → 0, chosen before n, f and δ; reason: the paper's "uniformly in f and δ"
--   - generalization: δ with 0 < δ ≤ 1 (Definition 2.4) → δ any real; reason: for δ ≤ 0 the bound only asks for agreement ≤ 1/2 (a constant affine map always gives 1/2); for δ > 1 the hypothesis exceeds 1 and is vacuous; the source case is included
--   - encoding: f : S → {±1}, signed characters σχ → f : F₂ⁿ → ZMod 2 (only values on the slice are queried or measured), affine maps x ↦ ⟨a,x⟩ + c, acceptance ∑ᵢ f(zᵢ) = 0; reason: σχ_ξ = (−1)^{⟨ξ,x⟩+c}; the product of ±1 answers is 1 iff the F₂ sum is 0; same instances
--   - encoding: for all sufficiently large n with pn even → ∃ N, ∀ n ≥ N, ∀ w : ℕ with (w : ℝ) = p·n and w even; reason: w is the integer pn; same instances
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.2.2, p. 49 (PDF 51), Corollary 6.15

import Mathlib
import Definitions.Def_SliceLinearity_Tests_SliceTests
import Definitions.Def_SliceLinearity_Tests_ActiveSet
import Definitions.Def_SliceLinearity_Tests_Transfer

set_option autoImplicit false

namespace SliceLinearity.Tests

open Filter Topology in
/-- **Corollary 6.15** (Sharp agreement on a biased slice), p. 49 (PDF 51). Fix `0 < p ≤ 1/2` and set
`k = 1 + ⌈1/p⌉`. For all sufficiently large `n` with `pn` even, the symmetric active-set test `λ_{p,k}`
conditioned on all queries lying in `S(pn)` is perfectly complete, also for affine maps when `k` is
even. If `f` passes it with probability at least `(1 + δ)/2`, then, uniformly in `f` and `δ`,
`max_{φ affine} agr_ν(f, φ) ≥ (1 + δ)/2 − o(1)`. -/
theorem corollary_6_15 (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℕ, (w : ℝ) = p * n → Even w →
      (∀ a : Cube n, accW (condWeight (lambdaPK p ⌈1 / p⌉₊) n w) (linMap a) = 1) ∧
      (Even (1 + ⌈1 / p⌉₊) → ∀ (a : Cube n) (c : ZMod 2),
        accW (condWeight (lambdaPK p ⌈1 / p⌉₊) n w) (affMap a c) = 1) ∧
      ∀ (f : Cube n → ZMod 2) (δ : ℝ),
        (1 + δ) / 2 ≤ accW (condWeight (lambdaPK p ⌈1 / p⌉₊) n w) f →
          (1 + δ) / 2 - ε n ≤ maxAffAgr (slice n w) f := by sorry

end SliceLinearity.Tests
