-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_lemma_2_1
-- name    : RandOrderKnapGAP.Integral.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:27:00.773718+00:00
-- url     : https://prove2.me/theorems/82e85fc9-2ceb-45b9-baf4-2629868cc5fd
-- title:
--   Lemma 2.1 — the last item of a uniformly ordered prefix is uniform, and its predecessors are a uniform ordering
-- statement:
--   Let $\pi$ be a uniformly random arrival order of $n$ items and $Q_k=\{\pi(1),\dots,\pi(k)\}$. Fix $k\ge1$ and a set $Q$ of $k$ items. Conditional on $Q_k=Q$, the current item $\pi(k)$ is uniform on $Q$:
--   $$\Pr\big(\pi(k)=i\mid Q_k=Q\big)=\frac1k\qquad(i\in Q).$$
--   Conditional further on $\pi(k)=i$, the preceding items $\pi(1),\dots,\pi(k-1)$ form a uniformly random ordering of $Q\setminus\{i\}$: every one of the $(k-1)!$ orderings has conditional probability $1/(k-1)!$.
--
--   This is the random-order fact used in every round of the analysis: once the unordered prefix is fixed, each of its members is equally likely to be the one being decided.
--
--   Differences from the source:
--   - encoding: rounds 1, …, k with current item π(k) → 0-based round r = k − 1 with current item π r and Q.card = r + 1; reason: Lean's Fin n indexing; same statement
--   - encoding: conditional probabilities over the uniform order; 'uniformly random ordering of Q \ {i}' → count ratios over Perm (Fin n); every injective f : Fin r → Q \ {i} (an ordering) has conditional probability 1/r!; reason: uniformity over the r! orderings is exactly this
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 4 (PDF 6), Lemma 2.1

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_RandomOrder

namespace RandOrderKnapGAP.Integral

/-- **Lemma 2.1** (the last item of a prefix), p. 4. Let `π` be a uniformly random permutation of
`n` items, let `r` be a (0-based) round, so `k = r + 1` items have arrived and `π r` is the
current item, and let `Q` be a set of `k` items. Conditional on `Q_k = Q`, the current item is
uniform on `Q`; conditional further on `π r = i`, the preceding items `π 0, …, π (r-1)` form a
uniformly random ordering of `Q \ {i}`: each of the `r!` orderings `f` has probability `1/r!`. -/
theorem lemma_2_1 (n : ℕ) (r : Fin n) (Q : Finset (Fin n)) (hQ : Q.card = r.val + 1) :
    (∀ i ∈ Q,
      condProbPerm (fun π => π r = i) (fun π => prefixSet π (r.val + 1) = Q)
        = 1 / ((r.val + 1 : ℕ) : ℝ)) ∧
    (∀ i ∈ Q, ∀ f : Fin r.val → Fin n, Function.Injective f → (∀ j, f j ∈ Q.erase i) →
      condProbPerm
          (fun π => ∀ j : Fin r.val, π ⟨j.val, lt_trans j.isLt r.isLt⟩ = f j)
          (fun π => prefixSet π (r.val + 1) = Q ∧ π r = i)
        = 1 / (Nat.factorial r.val : ℝ)) := by sorry

end RandOrderKnapGAP.Integral
