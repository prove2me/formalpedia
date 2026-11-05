-- Prove2me | Theorems.Thm_SecSampling_lemma_1
-- name    : SecSampling.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:29.681203+00:00
-- url     : https://prove2.me/theorems/c27f6b0f-3147-44e2-9d5a-19637f715fe3
-- title:
--   Lemma 1 — success probability of the $k$-max algorithm (corrected: $\ge kp^k(1-p)$, and $=kp^k(1-p)+p^n$ for increasing order, $n\ge k+1$)
-- statement:
--   Let $p\in(0,1)$, $k=\lfloor 1/(1-p)\rfloor$, and consider the $k$-max algorithm in AOSp with $n$ elements of distinct values.
--
--   1. If $n\le k$, then for every order of the online set chosen after sampling, the $k$-max algorithm picks the maximum online element with probability at least $kp^k(1-p)$.
--   2. If $n\ge k+1$, then for every order of the online set chosen after sampling this probability is at least
--   $$k\,p^{k}(1-p)+p^{n},$$
--   with equality when the online elements are presented in increasing order of value.
--
--   The term $p^n$ is the probability that every element is sampled, which counts as a win. Together the two parts give the guarantee half of Theorem 1 for every $n$, and part 2 shows the guarantee $kp^k(1-p)$ is approached as $n\to\infty$.
--
--   Differences from the source:
--   - correction: for a given p, k-max chooses the maximum online element with probability exactly ⌊1/(1−p)⌋ p^⌊1/(1−p)⌋ (1 − p) → for n ≤ k: at least kpᵏ(1−p); for n ≥ k+1: at least kpᵏ(1−p) + pⁿ for every order, with equality for increasing order; reason: the printed equality is false: for n = 1 the success probability is 1 (sampled: vacuous win; online: k-max accepts it); for p = 1/2, n = 3, increasing order it is 3/8 ≠ 1/4 because the all-sampled event pⁿ is a win (p.2); and an order other than increasing can do better (decreasing order: k-max wins whenever an online value exceeds the threshold), so only the inequality holds for every order
--   - encoding: n elements with values α₁, …, αₙ and "the maximum valued element in V" → an injective value vector v : Fin n → ℝ; reason: the maximum is unique only for distinct values, which the paper presupposes; elements are indexed by Fin n
--   - encoding: the order of V chosen by the adversary after sampling → any ord : Finset (Fin n) → List (Fin n) listing each online element once (IsOnlineOrder); reason: same adversary; footnote 5 says the lemma holds for orders chosen after sampling
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 1, p.5 (PDF p.6), with footnote 5

import Mathlib
import Definitions.Def_SecSampling_AOSp

namespace SecSampling

/-- **Lemma 1** (arXiv:2011.07869v1, p.5), corrected. The printed lemma says that k-max, with
`k = ⌊1/(1−p)⌋`, chooses the maximum online element with probability exactly `kpᵏ(1−p)`; that
fails for `n = 1` (the probability is `1`) and, through the vacuous win when everything is
sampled, for every `n`. Corrected statement:

(i) for `n ≤ k`, every injective value vector and every sample-dependent order of the online set,
the success probability is at least `kpᵏ(1−p)`;

(ii) for `n ≥ k + 1` and every injective value vector, the success probability is at least
`kpᵏ(1−p) + pⁿ` for every sample-dependent order, with equality when the online elements are
presented in increasing order of value.

**Formalization Note.** `pⁿ` is the probability that all elements are sampled, a win by vacuity
(p.2). -/
theorem lemma_1 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ n : ℕ, n ≤ kOf p → ∀ v : Fin n → ℝ, Function.Injective v →
      ∀ ord : Finset (Fin n) → List (Fin n), IsOnlineOrder ord →
        guarantee p ≤ winProb p (kmax p) v ord) ∧
    (∀ n : ℕ, kOf p + 1 ≤ n → ∀ v : Fin n → ℝ, Function.Injective v →
      (∀ ord : Finset (Fin n) → List (Fin n), IsOnlineOrder ord →
        guarantee p + p ^ n ≤ winProb p (kmax p) v ord) ∧
      (∀ ord : Finset (Fin n) → List (Fin n), IsOnlineOrder ord →
        (∀ S : Finset (Fin n), (ord S).Pairwise (fun x y => v x < v y)) →
        winProb p (kmax p) v ord = guarantee p + p ^ n)) := by sorry

end SecSampling
