-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_lemma_D_1
-- name    : SingleSampleCombPI.XOS.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:09:32.256808+00:00
-- url     : https://prove2.me/theorems/c1a65a5b-8ce7-42ad-9e00-cf6c8dd8cfc2
-- title:
--   Lemma D.1 — independent retention, approximate greedy, and the q = 1 bound
-- statement:
--   Consider the partition-matroid instance of Theorem 4.3 and let $O$ be an optimal solution of the original instance. Retain each part independently with probability $q\in[0,1]$ and run greedy on the retained parts in uniformly random order, obtaining $A$.
--
--   1. With exact greedy (ties arbitrary),
--   $$\mathbb E[f(A)]\ \ge\ \Big(q-\frac{q^2}{2}\Big)f(O).$$
--   2. If each greedy step selects an element within additive $\delta\ge0$ of $\max_{u\in P_i}f(u\mid A^-)$, then
--   $$\mathbb E[f(A)]\ \ge\ \Big(q-\frac{q^2}{2}\Big)\big(f(O)-\ell\delta\big).$$
--   3. When $q=1$, $\mathbb E[f(A)]\ge0.5096\,f(O)-O(\ell\delta)$: there is one constant $K\ge0$ such that for every instance, every $\delta\ge0$ and every $\delta$-approximate greedy rule, $\mathbb E[f(A)]\ge0.5096\,f(O)-K\ell\delta$.
--
--   Clause 1 gives the smooth ratio $\Gamma(q)=q-q^2/2$ of Algorithm 4.
--
--   Differences from the source:
--   - reading: O(ℓδ) in the q = 1 clause → ∃ K ≥ 0, quantified before the instance, the number of parts and δ, with error K·ℓ·δ; reason: the usual uniform meaning of the asymptotic notation; no numerical constant is given in the source
--   - reading: ties are broken arbitrarily → any online tie-breaking rule mapping the history of processed parts and the arriving part to a (δ-approximately) greedy choice; reason: the algorithm is online, so a tie may depend on the past but not on future arrivals
--   - encoding: finite ground set N → a finite type N : Type (universe 0); reason: every finite set is represented
--   - encoding: 0.5096 → 637/1250; reason: the same exact decimal
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 39 / PDF p. 41, Lemma D.1; proof PDF pp. 41–42

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_PartitionGreedy
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

namespace SingleSampleCombPI.XOS

/-- **Lemma D.1** (Chawla–Dang, STOC 2027 submission #30, printed p. 39 / PDF p. 41).  In the
partition-matroid instance of Theorem 4.3, retain each part independently with probability `q`
and run greedy on the retained parts in uniformly random order; `O` is an optimal solution of the
original instance.  (1) `E[f(A)] ≥ (q - q²/2) f(O)`.  (2) If every step is within additive
`δ ≥ 0` of the best marginal, `E[f(A)] ≥ (q - q²/2)(f(O) - ℓδ)`.  (3) For `q = 1`,
`E[f(A)] ≥ 0.5096 f(O) - O(ℓδ)`, with one universal constant in the `O(·)`. -/
theorem lemma_D_1 :
    (∀ {N : Type} [Fintype N] [DecidableEq N] {ℓ : ℕ} (P : Fin ℓ → Finset N), IsPartition P →
      ∀ f : Finset N → ℝ, (∀ S, 0 ≤ f S) → SetMonotone f →
      SubsamplingSM.Offline.IsSubmodular f → ∀ q ∈ Set.Icc (0 : ℝ) 1,
      ∀ rule : List (Fin ℓ) → Fin ℓ → N, IsApproxGreedyRule f P 0 rule →
        (q - q ^ 2 / 2) * optVal f P ≤ retainedGreedyExp f q rule) ∧
    (∀ {N : Type} [Fintype N] [DecidableEq N] {ℓ : ℕ} (P : Fin ℓ → Finset N), IsPartition P →
      ∀ f : Finset N → ℝ, (∀ S, 0 ≤ f S) → SetMonotone f →
      SubsamplingSM.Offline.IsSubmodular f → ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 ≤ δ →
      ∀ rule : List (Fin ℓ) → Fin ℓ → N, IsApproxGreedyRule f P δ rule →
        (q - q ^ 2 / 2) * (optVal f P - ℓ * δ) ≤ retainedGreedyExp f q rule) ∧
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {N : Type} [Fintype N] [DecidableEq N] {ℓ : ℕ} (P : Fin ℓ → Finset N), IsPartition P →
      ∀ f : Finset N → ℝ, (∀ S, 0 ≤ f S) → SetMonotone f →
      SubsamplingSM.Offline.IsSubmodular f → ∀ δ : ℝ, 0 ≤ δ →
      ∀ rule : List (Fin ℓ) → Fin ℓ → N, IsApproxGreedyRule f P δ rule →
        (637 / 1250 : ℝ) * optVal f P - K * (ℓ * δ) ≤ retainedGreedyExp f 1 rule := by sorry

end SingleSampleCombPI.XOS
