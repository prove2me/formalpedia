-- Prove2me | Theorems.Thm_Palvolgyi2026_kneser_tucker
-- name    : Palvolgyi2026.kneser_tucker
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T13:41:26.298987+00:00
-- url     : https://prove2.me/theorems/d7d55e2d-28a1-495f-a4f8-c295ba0dac28
-- title:
--   Pálvölgyi's Kneser–Tucker lemma (Lemma 15) — no cyclically equivariant labelling of P_p(n, k) by Z_p × [m] with the tie property when n − pk ≥ m − 1
-- statement:
--   Let $p = q + 1$ be a prime and $k, m \ge 1$ with $n - pk \ge m - 1$ (as integers). Let $\mathcal P_p(n,k)$ be the set of $p$-tuples $\mathcal A = (\mathcal A_0, \dots, \mathcal A_{p-1})$ of families of $k$-element subsets of $\{0, \dots, n-1\}$, not all empty, such that every member of one family is disjoint from every member of any other, ordered by coordinatewise inclusion. There is no labelling $\mu = (\mu_1, \mu_2)$ with values in $\mathbb Z_p \times [m]$ such that, on $\mathcal P_p(n,k)$,
--
--   - $\mu$ is equivariant: $\mu(\sigma \mathcal A) = (\mu_1(\mathcal A) + 1, \mu_2(\mathcal A))$, where $\sigma \mathcal A = (\mathcal A_{p-1}, \mathcal A_0, \dots, \mathcal A_{p-2})$;
--   - $\mu$ has the tie property: whenever $\mathcal A \le \mathcal B$ and $\mu_2(\mathcal A) = \mu_2(\mathcal B)$, also $\mu_1(\mathcal A) = \mu_1(\mathcal B)$.
--
--   Pálvölgyi, pp. 13–14: “For $p \ge 2$, let $\mathcal P_p(n,k)$ consist of tuples $\mathcal A = (\mathcal A_1, \dots, \mathcal A_p)$, where the $\mathcal A_i$ are families of $k$-subsets of $[n]$, not all empty, and every member of one coordinate family is disjoint from every member of any other. We order these tuples by coordinatewise inclusion, and $\mathbb Z_p$ acts by a cyclic shift.” “Lemma 15 (Kneser–Tucker lemma). Let $p$ be prime and let $m \ge 1$. Suppose that $\mu = (\mu_1, \mu_2) : \mathcal P_p(n,k) \longrightarrow \mathbb Z_p \times [m]$ is equivariant under cyclic shifts. Suppose moreover that whenever $\mathcal A \le \mathcal B$, $\mu_2(\mathcal A) = \mu_2(\mathcal B) \implies \mu_1(\mathcal A) = \mu_1(\mathcal B)$. (3) Then $n - pk < m - 1$. Equivalently, no such labeling exists if $n - pk \ge m - 1$.”
--
--   The paper proves it from Ziegler's $\mathbb Z_p$-Tucker lemma ([`Ziegler2002.zp_tucker`](https://prove2.me/theorems/744936d5-530f-4668-b5e5-d5c550aac395)) and uses it to prove the Kneser-shift theorem ([`Palvolgyi2026.kneser_shift`](https://prove2.me/theorems/88e50ee2-adbf-41ca-a769-564877b2c29d)).
--
--   **Formalization note.** The prime is written $q + 1$; families are `Finset (Finset (Fin n))`, coordinates and signs are indexed by `Fin (q + 1)` from $0$, and $[m]$ is `Fin m`. The integer inequality $n - pk \ge m - 1$ is the pair `m - 1 ≤ n - (q + 1) * k` and `(q + 1) * k ≤ n` in natural numbers. The labelling is given on all tuples of families, and equivariance and the tie property are assumed only on $\mathcal P_p(n,k)$. The hypothesis $k \ge 1$ is added; the paper's proof uses $\ell_0 = p(k-1) \ge 0$.
-- source:
--   Pálvölgyi, D., A nearcircumsphere-Ramsey theorem for solvable transitive configurations, arXiv:2608.10865v2 (2026), https://arxiv.org/abs/2608.10865, p. 14, Lemma 15 (Kneser–Tucker lemma)

import Mathlib

namespace Palvolgyi2026

theorem kneser_tucker (q : ℕ) (hp : (q + 1).Prime) (n k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hnk : m - 1 ≤ n - (q + 1) * k) (hpk : (q + 1) * k ≤ n)
    (μ : (Fin (q + 1) → Finset (Finset (Fin n))) → Fin (q + 1) × Fin m)
    (hμ : ∀ 𝒜 : Fin (q + 1) → Finset (Finset (Fin n)),
      (∀ i, ∀ A ∈ 𝒜 i, A.card = k) → (∀ i j, i ≠ j → ∀ A ∈ 𝒜 i, ∀ B ∈ 𝒜 j, Disjoint A B) →
      (∃ i, (𝒜 i).Nonempty) →
        μ (fun i => 𝒜 (i - 1)) = ((μ 𝒜).1 + 1, (μ 𝒜).2))
    (htie : ∀ 𝒜 ℬ : Fin (q + 1) → Finset (Finset (Fin n)),
      (∀ i, ∀ A ∈ 𝒜 i, A.card = k) → (∀ i j, i ≠ j → ∀ A ∈ 𝒜 i, ∀ B ∈ 𝒜 j, Disjoint A B) →
      (∃ i, (𝒜 i).Nonempty) →
      (∀ i, ∀ A ∈ ℬ i, A.card = k) → (∀ i j, i ≠ j → ∀ A ∈ ℬ i, ∀ B ∈ ℬ j, Disjoint A B) →
      (∃ i, (ℬ i).Nonempty) →
      𝒜 ≤ ℬ → (μ 𝒜).2 = (μ ℬ).2 → (μ 𝒜).1 = (μ ℬ).1) :
    False := by
  sorry

end Palvolgyi2026
