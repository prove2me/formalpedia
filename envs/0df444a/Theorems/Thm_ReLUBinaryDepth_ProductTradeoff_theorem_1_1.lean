-- Prove2me | Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_theorem_1_1
-- name    : ReLUBinaryDepth.ProductTradeoff.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:25.434928+00:00
-- url     : https://prove2.me/theorems/e4309bf5-09ef-47ab-850d-55cfb9394983
-- title:
--   Theorem 1.1 — Exact realization and the all-depth size–depth tradeoff
-- statement:
--   For every $n\ge0$, $B>1$ and fixed constants $\theta_i(0),\theta_i(1)\in[0,B]$, put $P(x)=\prod_i\theta_i(x_i)$. The following three clauses hold together.
--
--   1. Without an independence hypothesis, there is a network $N$ with ReLU output such that
--   $$\operatorname{depth}(N)=n+1,\qquad \operatorname{width}(N)\le2,\qquad N(x)=P(x)\ \text{for every Boolean }x.$$
--   2. There is one absolute $C>0$, independent of $n,B,\theta$ and every network parameter. If the indexed family $(P(x))_{x\in\{0,1\}^n}$ is linearly independent over $\mathbb Q$, every exact network $N$ and width bound $w\ge n$ with $\operatorname{width}(N)\le w$ satisfy
--   $$2^n\le Cw^{\operatorname{depth}(N)}.$$
--   3. Let $B_n$, $\theta^{(n)}$, and networks $N_n$ be families indexed by $n\in\mathbb N$. Assume eventually that $B_n>1$, all coefficients lie in $[0,B_n]$, the Boolean-indexed product values are rationally linearly independent, and $N_n$ computes that product exactly. If
--   $$\operatorname{depth}(N_n)=o(n/\log n),$$
--   then there are no fixed $A>0$ and $k\in\mathbb N$ for which $\operatorname{width}(N_n)\le A(n+1)^k$ eventually. There is no assumption $n\le\operatorname{width}(N_n)$ in this family clause.
--
--   The theorem gives both exact constant-width realizability and an exponential tradeoff for arbitrary real weights and biases. Indexed independence retains all $2^n$ assignments; repeated outputs cannot be discarded before testing it.
--
--   Differences from the source:
--   - reading: network syntax and input-terminal counting are unspecified → raw Boolean inputs are available at every layer and are excluded from computational width; reason: Lemma 2.2 reads a fresh input at each stage while claiming constant width and counts the final summation gate
--   - generalization: ReLU network with the construction using adjacent computed layers → competitors may use every earlier computed layer and an affine final-output mode; reason: ordinary layered ReLU networks embed by setting extra weights to zero and selecting ReLU output; the uniform output-span bound also holds for the broader class
--   - generalization: n coordinates indexed from 1 to n → n may also be zero, with empty product 1 and a single final output ReLU; reason: this adds an empty-input case and preserves every positive-dimensional instance
--   - encoding: constant width in the realization clause → a uniform width bound 2 with an actual ReLU output gate; reason: the source construction uses two units per product layer and one final summation unit
--   - encoding: depth d and width w → depth is the number of hidden layers plus one and w is any upper bound on the computed maximum layer width; reason: the final output gate counts as one layer and one unit; raw inputs do not count
--   - encoding: O(w^d) and Omega(2^n) → one positive real constant before every input size, network and resource parameter; reason: this makes the source asymptotic constants absolute without changing the rate
--   - encoding: depth o(n/log n) and width polynomial in n → little-o at the natural-number atTop filter and an eventual bound A(n+1)^k with fixed A>0 and natural k; reason: finite prefixes and replacing n by n+1 do not affect either asymptotic condition; no n<=width assumption is imposed on the consequence
-- source:
--   Neil Krishnan, Elchanan Mossel, STOC 2027 submission #1645 (October 2026), Theorem 1.1, PDF p. 2 = printed p. 2; proof p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Construction

namespace ReLUBinaryDepth.ProductTradeoff

/-- Theorem 1.1, PDF = printed p.2, proof p.5: both clauses and the family consequence.
No independence is required in the realization clause. -/
theorem theorem_1_1 :
    (∀ (n : ℕ) (B : ℝ) (θ : Fin n → Bool → ℝ), Admissible B θ →
      ∃ N : Network n, N.depth = n + 1 ∧ N.width ≤ 2 ∧
        N.outputRelu = true ∧ N.Computes (productMap θ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (B : ℝ) (θ : Fin n → Bool → ℝ),
      Admissible B θ → LinearIndependent ℚ (productMap θ) →
      ∀ (N : Network n) (w : ℕ), n ≤ w → N.width ≤ w →
        N.Computes (productMap θ) → (2 : ℝ) ^ n ≤ C * (w : ℝ) ^ N.depth) ∧
    (∀ (B : ℕ → ℝ) (θ : (n : ℕ) → Fin n → Bool → ℝ)
        (N : (n : ℕ) → Network n),
      (∀ᶠ n in Filter.atTop,
        Admissible (B n) (θ n) ∧ LinearIndependent ℚ (productMap (θ n)) ∧
          (N n).Computes (productMap (θ n))) →
      Asymptotics.IsLittleO Filter.atTop
        (fun n : ℕ => ((N n).depth : ℝ))
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) →
      ¬ ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ,
        ∀ᶠ n in Filter.atTop, ((N n).width : ℝ) ≤ A * ((n : ℝ) + 1) ^ k) := by sorry

end ReLUBinaryDepth.ProductTradeoff
