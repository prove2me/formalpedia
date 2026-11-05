-- Prove2me | Theorems.Thm_SecSampling_theorem_1
-- name    : SecSampling.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:25.825939+00:00
-- url     : https://prove2.me/theorems/c8e6e0bc-71a9-4dec-a431-844d9c35e665
-- title:
--   Theorem 1 — the $k$-max algorithm with $k=\lfloor 1/(1-p)\rfloor$ has the optimal success guarantee $kp^k(1-p)$ for AOSp
-- statement:
--   Let $p\in(0,1)$ and $k=\lfloor 1/(1-p)\rfloor$. In the adversarial-order secretary problem with $p$-sampling:
--
--   1. **(The guarantee.)** For every number $n$ of elements, all distinct values, and every order of the online set chosen by an adversary who knows the values and the sampled set, the $k$-max algorithm picks the maximum online element with probability at least
--   $$k\,p^{k}(1-p).$$
--   2. **(Optimality.)** For every ordinal, possibly randomized algorithm $A$, which may know $n$ and $p$, and every $\varepsilon>0$, there are $n$ and distinct values on which $A$ succeeds with probability less than $k\,p^{k}(1-p)+\varepsilon$, even when the online elements arrive in a fixed order (by index) chosen before sampling.
--
--   Together: the success guarantee of the $k$-max algorithm is exactly $kp^k(1-p)$, and no algorithm has a larger one. For $p=1/2$ this is $1/4$; as $p\to1$ it tends to $1/e$.
--
--   Differences from the source:
--   - generalization: the adversary chooses the order σ knowing the sets S and V (p.2) → in part 2 the online elements arrive in index order, fixed before sampling; reason: a fixed order is one admissible AOSp adversary, so the bound against it implies the printed one; footnote 3 says the upper bounds hold for such an adversary
--   - reading: no algorithm can achieve a better success guarantee → every ordinal, possibly randomized algorithm, which may depend on n and p; reason: p.2: "All algorithms considered in this paper are ordinal ... plus, possibly, on some external randomness"; p.14: the result holds "allowing the player to have even exact knowledge of the length n"
--   - encoding: an ordinal algorithm, deciding on the relative rankings of the values seen so far plus possibly external randomness (p.2) → a function A n |S| h ∈ [0,1], the stopping probability given n, the number of samples and the ordinal history h (for each online element so far: the number of samples above it and of earlier online elements above it); reason: behavioural randomization is equivalent to any external randomness under perfect recall (Kuhn); the pairs determine exactly the relative order of the samples and the online elements seen so far
--   - encoding: n elements with values α₁, …, αₙ and "the maximum valued element in V" → an injective value vector v : Fin n → ℝ; reason: the maximum is unique only for distinct values, which the paper presupposes; elements are indexed by Fin n
--   - encoding: success guarantee = infimum over n and over the values of the success probability → part 1: a lower bound for every n, values and order; part 2: for every ε > 0 an instance below kpᵏ(1−p) + ε; reason: this is the infimum statement without real infima, which return 0 on empty or unbounded families
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Theorem 1, p.14 (PDF p.15); first stated p.5 (PDF p.6); model p.2 (PDF p.3)

import Mathlib
import Definitions.Def_SecSampling_AOSp

namespace SecSampling

/-- **Theorem 1** (Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, *The Secretary
Problem with Independent Sampling*, arXiv:2011.07869v1, p.14; first stated p.5). Let
`k = ⌊1/(1−p)⌋`. Then the k-max algorithm achieves a guarantee of `kpᵏ(1−p)` for AOSp.
Furthermore, no algorithm can achieve a better success guarantee.

(a) For every size `n`, all distinct values `v`, and every order of the online set chosen by an
adversary who sees the sampled set, k-max succeeds with probability at least `kpᵏ(1−p)`.

(b) For every ordinal, possibly randomized algorithm `A` (which may depend on `n` and `p`) and
every `ε > 0`, there are a size `n` and distinct values `v` on which `A` succeeds with probability
less than `kpᵏ(1−p) + ε` when the online elements arrive in index order.

**Formalization Note.** Values are injective `v : Fin n → ℝ`. The success guarantee (an infimum
over `n` and the values, p.2) is stated in ε-form. In (b) the order is fixed before sampling, an
adversary weaker than AOSp's (footnote 3, p.2), so (b) is stronger than the printed claim. -/
theorem theorem_1 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ (n : ℕ) (v : Fin n → ℝ), Function.Injective v →
      ∀ ord : Finset (Fin n) → List (Fin n), IsOnlineOrder ord →
        guarantee p ≤ winProb p (kmax p) v ord) ∧
    (∀ A : Algorithm, IsAlgorithm A → ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (v : Fin n → ℝ), Function.Injective v ∧
        winProb p A v (indexOrder n) < guarantee p + ε) := by sorry

end SecSampling
