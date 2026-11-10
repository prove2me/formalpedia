-- Prove2me | Theorems.Thm_SliceLinearity_Tests_theorem_1_1
-- name    : SliceLinearity.Tests.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:37:53.066535+00:00
-- url     : https://prove2.me/theorems/36834ead-bc27-4b46-bd9a-2d72737f7d12
-- title:
--   Theorem 1.1 — perfectly complete (1+⌈1/p⌉)-query tests on S(pn) and (r+1)/(2r+2)-query tests on S(r) with affine agreement (1+δ)/2 − o(1)
-- statement:
--   Let $S$ and $k$ be as in one of the following cases.
--
--   - **(i) Linear weight.** $S=S(pn)$, where $0<p\le1/2$ is a constant, $pn$ is even, and $k=1+\lceil1/p\rceil$.
--   - **(ii) Constant weight.** $S=S(r)$, where $r\ge2$ is fixed, and $k=r+1$ if $r$ is even, $k=2r+2$ if $r$ is odd.
--
--   Then, for all sufficiently large $n$, there is a perfectly complete $k$-query test on $S$ such that, if $f$ passes it with probability at least $(1+\delta)/2$, some affine map agrees with $f$ on at least a $(1+\delta)/2-o(1)$ fraction of $S$.
--
--   The test is a parity test: a distribution on zero-sum $k$-tuples of $S$, fixed before $f$, which accepts when $\sum_if(x_i)=0$ (Theorem 6.1: "parity testing on slices"). The $o(1)$ is a sequence $\varepsilon_n\to0$ that depends only on $p$ (resp. $r$) and is chosen before $n$, the test, $f$ and $\delta$. The paper proves case (i) as Corollary 6.15 and case (ii) from Proposition 6.17 (Theorem 6.1, printed pp. 36–37, PDF 38–39).
--
--   Differences from the source:
--   - reading: o(1) → ε : ℕ → ℝ with ε → 0, depending only on p (resp. r), chosen before n, the test, f and δ; reason: Theorem 6.1: "with p or r fixed as n → ∞"; Corollary 6.15, Theorem 6.6: "uniformly in f and δ"
--   - reading: 0 < p ≤ 1/2 a constant → p : ℚ; reason: Theorem 6.1(i) and Table 1 fix p rational; for irrational p no positive n has pn an integer, so no instance is lost
--   - reading: k-query test → k-query parity test (ParityTest: a distribution on zero-sum tuples of S^k fixed before f); reason: Theorem 6.1 states the result for "parity testing on slices"; both tests the paper builds are parity tests
--   - generalization: δ with 0 < δ ≤ 1 (Definition 2.4) → δ any real; reason: for δ ≤ 0 a constant affine map agrees on at least 1/2; for δ > 1 the hypothesis is vacuous; the source case is included
--   - encoding: f : S → F₂ → f : F₂ⁿ → ZMod 2; reason: the test only queries points of S and agreement is measured on S, so values off S are irrelevant
--   - encoding: for all sufficiently large n (with pn even) → ∃ N, ∀ n ≥ N, ∀ w : ℕ with (w : ℚ) = p·n and w even; reason: w is the integer pn; same instances
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §1.1, p. 2 (PDF 4), Theorem 1.1 = Theorem 6.1(i)–(ii), pp. 36–37 (PDF 38–39)

import Mathlib
import Definitions.Def_SliceLinearity_Tests_SliceTests

set_option autoImplicit false

namespace SliceLinearity.Tests

open Filter Topology in
/-- **Theorem 1.1** (Tests on slices; Theorem 6.1), p. 2 (PDF 4). Let `S` and `k` be as in one of the
following cases. (i) Linear weight: `S = S(pn)`, `0 < p ≤ 1/2` a (rational) constant, `pn` even,
`k = 1 + ⌈1/p⌉`. (ii) Constant weight: `S = S(r)`, `r ≥ 2` fixed, `k = r + 1` if `r` is even and `2r + 2` if `r`
is odd. Then, for all sufficiently large `n`, there is a perfectly complete `k`-query (parity) test on `S`
such that, if `f` passes it with probability at least `(1 + δ)/2`, some affine map agrees with `f` on
at least a `(1 + δ)/2 − o(1)` fraction of `S`; the `o(1)` depends only on `p` (resp. `r`). -/
theorem theorem_1_1 :
    (∀ p : ℚ, 0 < p → p ≤ 1 / 2 →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℕ,
        (w : ℚ) = p * n → Even w →
        ∃ T : ParityTest n (1 + ⌈1 / p⌉₊) (slice n w), T.PerfectlyComplete ∧
          ∀ (f : Cube n → ZMod 2) (δ : ℝ), (1 + δ) / 2 ≤ T.accProb f →
            ∃ (a : Cube n) (c : ZMod 2), (1 + δ) / 2 - ε n ≤ agreement (slice n w) f (affMap a c)) ∧
    (∀ r : ℕ, 2 ≤ r →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ N : ℕ, ∀ n ≥ N,
        ∃ T : ParityTest n (if Even r then r + 1 else 2 * r + 2) (slice n r), T.PerfectlyComplete ∧
          ∀ (f : Cube n → ZMod 2) (δ : ℝ), (1 + δ) / 2 ≤ T.accProb f →
            ∃ (a : Cube n) (c : ZMod 2), (1 + δ) / 2 - ε n ≤ agreement (slice n r) f (affMap a c)) := by sorry

end SliceLinearity.Tests
