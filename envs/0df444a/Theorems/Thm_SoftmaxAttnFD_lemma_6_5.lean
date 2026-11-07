-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_6_5
-- name    : SoftmaxAttnFD.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:49.664482+00:00
-- url     : https://prove2.me/theorems/83a2bf6a-fc10-49d9-b8d0-0d2b71d5a62c
-- title:
--   Lemma 6.5, p.24 — properties of the perturbed envelope
-- statement:
--   Let $d\ge3$. There are constants $c,C_{\rm bits}$ depending only on $d$ with the following property. Let $\lambda,U,N_\Sigma\ge1$ be integers, $\emptyset\ne\Sigma_0\subseteq[N_\Sigma]$, $y_s\in\mathbb Q^d$ with $\|y_s\|_\infty\le U$ and bit length at most $\lambda$, $\log_2(N_\Sigma+2)\le\lambda$, $\log_2(U+2)\le\lambda$, and let $\tilde f_s,P(\cdot)$ come from the perturbed family with $\delta=2^{-c\lambda}$. Then:
--
--   1. $|\tilde f_s(u)-f_s(u)|\le1/8$ for every $s\in\Sigma_0$ and every real $u$ with $\|u\|_\infty\le U$.
--   2. Let $u\in\mathbb Q^{d-1}$ with $\|u\|_\infty\le U$ have bit length at most $\lambda$, and $\emptyset\ne\Sigma'\subseteq\Sigma_0$. Every $s\in\Sigma'$ that maximizes $\tilde f_s(u)$ over $\Sigma'$ also maximizes $f_s(u)$ over $\Sigma'$.
--   3. The family is capped over $\Sigma_0$ and $U$: its hyperplanes are in general position, each $P(\Sigma')$ is bounded with nonempty interior, and a common height separates sources from caps on the box. All constraint coefficients and all vertices of each $P(\Sigma')$ have at most $C_{\rm bits}\lambda$ bits.
--
--   Differences from the source:
--   - generalization: clause (c) as printed → also the height of the capped family (Lemma A.7(a) and §A.7, p.44); general position of all |Σ₀| + d constraints at once; reason: the page's proof establishes both, and each subfamily inherits general position
--   - encoding: "bit length at most λ" of a point, "admissible", O_d(λ) bits → every coordinate has at most λ bits; every coordinate has at most C_bits·λ bits, with C_bits depending only on d; reason: the two readings of a point's bit length differ by a factor d, which the constants absorb
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 6.5, p.24; Definition 6.4, p.24; §A.7, p.44

import Definitions.Def_SoftmaxAttnFD_perturbedFamily

namespace SoftmaxAttnFD

/-- **Lemma 6.5** (arXiv:2611.06055, sha256 a60f7609…, p.24), on the setup of Definition 6.4 (p.24) and
the concrete family of §A.7 (p.44). `c` is the perturbation constant, and it depends only on `d`.

**Formalization Note** Clause (c) is `IsCappedFamily`, which also records the height `Z_top` of
Lemma A.7(a) and the §A.7 proof, plus the two bit bounds. `O_d(λ)` is `Cbits · λ`, with `Cbits`
depending only on `d`. "Admissible" (§2.1, §6) means the target's encoding length is at most `λ`. -/
theorem lemma_6_5 (d : ℕ) (hd : 3 ≤ d) :
    ∃ c Cbits : ℕ, 0 < c ∧
      ∀ (lam U N : ℕ) (S₀ : Finset ℕ) (y : ℕ → Src d),
        1 ≤ lam → 1 ≤ U → 1 ≤ N → S₀.Nonempty → (∀ s ∈ S₀, 1 ≤ s ∧ s ≤ N) →
        (∀ s ∈ S₀, SrcBits (y s) lam) →
        (∀ s ∈ S₀, (∀ i, |(y s).1 i| ≤ (U : ℚ)) ∧ |(y s).2| ≤ (U : ℚ)) →
        Real.logb 2 ((N : ℝ) + 2) ≤ lam → Real.logb 2 ((U : ℝ) + 2) ≤ lam →
        (∀ s ∈ S₀, ∀ u : Fin (d - 1) → ℝ, InBox U u →
          |evalSrc ((perturbedFamily c lam U y).src s) u - evalSrc (y s) u| ≤ 1 / 8) ∧
        (∀ (u : Fin (d - 1) → ℚ) (S' : Finset ℕ), InBox U (fun i => (u i : ℝ)) →
          (∀ i, ratBits (u i) ≤ lam) → S'.Nonempty → S' ⊆ S₀ → ∀ s ∈ S',
          (∀ s' ∈ S', evalSrc ((perturbedFamily c lam U y).src s') (fun i => (u i : ℝ)) ≤
            evalSrc ((perturbedFamily c lam U y).src s) (fun i => (u i : ℝ))) →
          ∀ s' ∈ S', evalSrc (y s') (fun i => (u i : ℝ)) ≤ evalSrc (y s) (fun i => (u i : ℝ))) ∧
        IsCappedFamily (perturbedFamily c lam U y) S₀ U ∧
        (∀ s ∈ S₀, SrcBits ((perturbedFamily c lam U y).src s) (Cbits * lam)) ∧
        (∀ h, SrcBits ((perturbedFamily c lam U y).cap h) (Cbits * lam)) ∧
        (∀ S' : Finset ℕ, S'.Nonempty → S' ⊆ S₀ →
          ∀ v ∈ ((perturbedFamily c lam U y).polytope S').extremePoints ℝ,
            ∃ w : Src d, v = ((fun i => (w.1 i : ℝ)), (w.2 : ℝ)) ∧ SrcBits w (Cbits * lam)) := by sorry

end SoftmaxAttnFD
