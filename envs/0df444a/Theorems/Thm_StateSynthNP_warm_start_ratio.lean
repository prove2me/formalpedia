-- Prove2me | Theorems.Thm_StateSynthNP_warm_start_ratio
-- name    : StateSynthNP.warm_start_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:48:47.589818+00:00
-- url     : https://prove2.me/theorems/62064160-dd8e-4b30-8c5f-a45d38999936
-- title:
--   Warm-start ratio guarantee $p_x/2\le q_x\le 2p_x$ from $(1\pm\gamma)$ prefix-sum estimates
-- statement:
--   Let $B$ be a finite alphabet, $m\in\mathbb N$, and $p\ge0$ a probability distribution on $B^m$ with prefix sums $s_y$. Let $\hat s_y$ be estimates with
--
--   $$
--   (1-\gamma)\,s_y\le\hat s_y\le(1+\gamma)\,s_y\qquad\text{for every word }y\text{ of length at most }m,
--   $$
--
--   where $0\le\gamma$ and $4m\gamma\le1$. Then the warm-start weights $q_x$ (products of the normalized conditional ratios of the estimates along $x$) satisfy
--
--   $$
--   \sum_x q_x=1\qquad\text{and}\qquad \frac{p_x}{2}\le q_x\le 2p_x\quad\text{for every }x .
--   $$
--
--   This is the guarantee $\sqrt{p_x/2}\le\sqrt{q_x}\le\sqrt{2p_x}$ that makes the rejection-sampling rotation (5) well defined and balanced. In the paper the $n$ qubits are batched into $m=n/\log n$ blocks of $\log n$ qubits, so the condition is $\gamma\le\log n/(4n)$, the paper's $\gamma=\Theta(\log n/n)$.
--
--   Differences from the source:
--
--   - generalization: n qubits batched into m = n/log n blocks of log n qubits → any finite alphabet B and any number m of levels; reason: B = {0,1}^{log n} and m = n/log n specialize it to the source
--   - reading: γ = Θ(log n/n) → any γ with 0 ≤ γ and 4mγ ≤ 1; reason: Θ asserts that some constant works; with m = n/log n this is γ ≤ log n/(4n), and a large constant fails since ((1+γ)/(1−γ))^m grows like e^{2γm}
--   - reading: q_x is a product of ratios of approximate prefix sums → ratios normalized by the sum of the sibling estimates, ŝ_{yb}/Σ_{b'} ŝ_{yb'}; reason: the conditional rotations must be unitary, which forces this normalization
--   - generalization: the guarantee √(p_x/2) ≤ √q_x ≤ √(2p_x) → p_x/2 ≤ q_x ≤ 2p_x together with Σ_x q_x = 1; reason: equivalent for nonnegative values; the normalization of the warm-start state, implicit in the paper, is stated as an extra clause
-- source:
--   A. Sen, State Synthesis with an NP oracle, arXiv:2611.02370 (held version, sha256 1705b965726e24478266bc8bdb695f0c6c6e06e172eff71c247272c116f264d0), proof of Theorem 2.1, p.4 ("√(p_x/2) ≤ √q_x ≤ √(2p_x)"); proof of Lemma 2.2, p.4 ("Each q_x is a product of O(n/ log n) ratios of approximate prefix sums, so estimating every prefix sum to within a factor (1 ± γ) with γ = Θ(log n/n) guarantees this")

import Mathlib
import Definitions.Def_StateSynthNP_warmStart

set_option autoImplicit false

namespace StateSynthNP

/-- **The warm-start ratio guarantee.** "each q_x is obtained through a product of sufficiently good
approximate prefix-sums such that it satisfies the guarantee that √(p_x/2) ≤ √q_x ≤ √(2p_x)", and
"Each q_x is a product of O(n/ log n) ratios of approximate prefix sums, so estimating every prefix
sum to within a factor (1 ± γ) with γ = Θ(log n/n) guarantees this".

Source: A. Sen, *State Synthesis with an NP oracle*, arXiv:2611.02370 (held version, sha256 1705b965…), proof of Theorem 2.1, p.4, and proof of Lemma 2.2, p.4.

Statement: let `p ≥ 0` be a probability distribution on strings of `m` symbols from a finite
alphabet `B` (blocks of qubits), with prefix sums `s_y`. Let `ŝ_y` be estimates with
`(1 − γ) s_y ≤ ŝ_y ≤ (1 + γ) s_y` for every prefix `y` of length at most `m`, where `0 ≤ γ` and
`4 m γ ≤ 1`. Then the warm-start weights `q_x` (products of the normalized conditional ratios) form a
probability distribution and `p_x / 2 ≤ q_x ≤ 2 p_x` for every `x`.

**Formalization Note.** `Θ(log n/n)` is made explicit: with `m = n / log n` levels, `γ ≤ 1/(4m)` is
`γ ≤ log n/(4n)`; then `((1+γ)/(1−γ))^m ≤ e^{2/3} < 2`. -/
theorem warm_start_ratio {B : Type} [Fintype B] [DecidableEq B] (m : ℕ)
    (p : (Fin m → B) → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (sh : List B → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : 4 * (m : ℝ) * γ ≤ 1)
    (hest : ∀ y : List B, y.length ≤ m →
      (1 - γ) * prefixSum p y ≤ sh y ∧ sh y ≤ (1 + γ) * prefixSum p y) :
    ∑ x : Fin m → B, warmStart sh x = 1 ∧ ∀ x : Fin m → B, p x / 2 ≤ warmStart sh x ∧ warmStart sh x ≤ 2 * p x := by sorry

end StateSynthNP
