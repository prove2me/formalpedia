-- Prove2me | Theorems.Thm_SliceLinearity_Tests_theorem_6_6
-- name    : SliceLinearity.Tests.theorem_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:40:50.819172+00:00
-- url     : https://prove2.me/theorems/838f8569-53dd-4994-8e86-294b0761dc82
-- title:
--   Theorem 6.6 — a biased-cube tester meeting the transfer conditions gives a perfectly complete slice tester with the same soundness up to o(1)
-- statement:
--   Fix $0<p<1$ and $k\ge3$. Let a $k$-query $p$-biased tester $\lambda$ satisfy Definition 6.7 and have a continuous soundness guarantee $s$, with $s(0)=0$. Then for all sufficiently large $n$ with $pn$ even, its conditioned test on $S(pn)$ is perfectly complete, and also complete for signed characters when $k$ is even. Moreover, if $f$ passes this test with probability at least $(1+\delta)/2$, then, uniformly in $f$ and $\delta$,
--   $$\max_{\chi,\ \sigma\in\{\pm1\}}\mathrm{agr}_\nu(f,\sigma\chi)\ge\frac{1+s(\delta)}2-o(1),$$
--   where $\nu$ is uniform on $S(pn)$.
--
--   Differences from the source:
--   - reading: o(1) uniformly in f and δ → ε : ℕ → ℝ with ε → 0, chosen before n, f and δ; reason: the paper's "uniformly in f and δ"
--   - encoding: continuous soundness guarantee s with s(0) = 0; δ → s continuous on [0, 1], s 0 = 0, the guarantee for 0 < δ ≤ 1 in every dimension; the conclusion for 0 < δ ≤ 1; reason: the paper's convention 0 < δ ≤ 1 (Definition 2.4, p. 9), where s is used
--   - encoding: f : S → {±1}, signed characters σχ → f : F₂ⁿ → ZMod 2 (only values on the slice are queried or measured), affine maps x ↦ ⟨a,x⟩ + c, acceptance ∑ᵢ f(zᵢ) = 0; reason: σχ_ξ = (−1)^{⟨ξ,x⟩+c}; the product of ±1 answers is 1 iff the F₂ sum is 0; same instances
--   - encoding: for all sufficiently large n with pn even → ∃ N, ∀ n ≥ N, ∀ w : ℕ with (w : ℝ) = p·n and w even; reason: w is the integer pn; same instances
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.2, p. 42 (PDF 44), Theorem 6.6; proof pp. 46–47 (PDF 48–49)

import Mathlib
import Definitions.Def_SliceLinearity_Tests_SliceTests
import Definitions.Def_SliceLinearity_Tests_BiasedAnalysis
import Definitions.Def_SliceLinearity_Tests_Transfer

set_option autoImplicit false

namespace SliceLinearity.Tests

open Filter Topology in
/-- **Theorem 6.6** (From a biased tester to a slice tester), p. 42 (PDF 44). Fix `0 < p < 1`, `k ≥ 3`
and a `k`-query `p`-biased tester `λ` satisfying Definition 6.7 with a continuous soundness guarantee
`s`, `s(0) = 0`. For all sufficiently large `n` with `pn` even, its conditioned test on `S(pn)` is
perfectly complete, also for signed characters (affine maps) when `k` is even; and if `f` passes it
with probability at least `(1 + δ)/2`, then, uniformly in `f` and `δ`,
`max_{χ,σ} agr_ν(f, σχ) ≥ (1 + s(δ))/2 − o(1)`, `ν` uniform on `S(pn)`. -/
theorem theorem_6_6 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k : ℕ) (hk : 3 ≤ k)
    (lam : (Fin k → ZMod 2) → ℝ) (hlam : IsBiasedTester p lam) (htr : TransferConditions p lam)
    (s : ℝ → ℝ) (hs : ContinuousOn s (Set.Icc 0 1)) (hs0 : s 0 = 0)
    (hsound : SoundnessGuarantee p lam s) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℕ, (w : ℝ) = p * n → Even w →
      (∀ a : Cube n, accW (condWeight lam n w) (linMap a) = 1) ∧
      (Even k → ∀ (a : Cube n) (c : ZMod 2), accW (condWeight lam n w) (affMap a c) = 1) ∧
      ∀ (f : Cube n → ZMod 2) (δ : ℝ), 0 < δ → δ ≤ 1 →
        (1 + δ) / 2 ≤ accW (condWeight lam n w) f →
          (1 + s δ) / 2 - ε n ≤ maxAffAgr (slice n w) f := by sorry

end SliceLinearity.Tests
