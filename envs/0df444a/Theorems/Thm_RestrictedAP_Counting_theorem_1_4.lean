-- Prove2me | Theorems.Thm_RestrictedAP_Counting_theorem_1_4
-- name    : RestrictedAP.Counting.theorem_1_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:19:57.788202+00:00
-- url     : https://prove2.me/theorems/4e3ed6a8-ade9-4c06-8a7a-546715a0dd8f
-- title:
--   Theorem 1.4 — counting lemma for distributions on $\Sigma^3$ with diagonal support and no $(\mathbb Z,+)$-embedding
-- statement:
--   For all $m\in\mathbb N$, $s>0$ and $\alpha>0$ there is $\beta=\beta(\alpha,m,s)>0$ such that the following holds. Let $\Sigma$ be an alphabet of size at most $m$, $\mu$ a distribution on $\Sigma^3$ and $\nu$ a distribution on $\Sigma$ such that
--
--   1. the marginal of $\mu$ on each coordinate equals $\nu$, and $(x,x,x)\in\mathrm{supp}(\mu)$ for every $x\in\Sigma$;
--   2. every atom of $\mu$ has probability at least $s$;
--   3. $\mu$ has no $(\mathbb Z,+)$-embedding.
--
--   Then there is $n_0$ such that for every $n\ge n_0$ and every $A\subseteq\Sigma^n$ with $\nu^{\otimes n}(A)\ge\alpha$,
--   $$\Pr_{(x,y,z)\sim\mu^{\otimes n}}\big[x,y,z\in A\big]\ \ge\ \beta .$$
--
--   This is the paper's general theorem; Theorem 1.2 is its case $\Sigma=\mathbb F_p$, $\mu=\mu_p$.
--
--   Differences from the source:
--   - reading: condition 1: (x, x, x) ∈ supp(μ) with x free → (x, x, x) ∈ supp(μ) for every x ∈ Σ; reason: the form used in Lemmas 3.6–3.8 and in the proof (Claim 5.14 restricts x, y, z to the same value)
--   - reading: 'there exists β = β(α, m, s) > 0 such that for sufficiently large n' → β is chosen after m, s, α and before Σ, μ, ν; n₀ is chosen after Σ, μ, ν; reason: only β is annotated with its dependencies; n₀ is not
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
--   - encoding: an alphabet Σ of size at most m → a type Σ with `Fintype`, `DecidableEq`, `Fintype.card Σ ≤ m`; reason: finite alphabet
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 3, Theorem 1.4

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions

namespace RestrictedAP.Counting

/-- **Theorem 1.4** (p. 3). For all `m`, `s > 0` and `α > 0` there is `β = β(α, m, s) > 0` such
that: for every alphabet `Σ` with `|Σ| ≤ m`, every distribution `μ` on `Σ^3` and `ν` on `Σ` with
(1) every marginal of `μ` equal to `ν` and `(x, x, x) ∈ supp(μ)` for every `x ∈ Σ`, (2) every
atom of `μ` of probability at least `s`, (3) no `(ℤ,+)`-embedding of `μ`, there is `n₀` such
that for all `n ≥ n₀` and every `A ⊆ Σ^n` with `ν^{⊗n}(A) ≥ α`,
`Pr_{(x,y,z) ∼ μ^{⊗n}} [x, y, z ∈ A] ≥ β`. -/
theorem theorem_1_4 (m : ℕ) (s α : ℝ) (hs : 0 < s) (hα : 0 < α) :
    ∃ β : ℝ, 0 < β ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig ≤ m →
      ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ → IsDist ν →
        (∀ i : Fin 3, marginal μ i = ν) → (∀ x : Sig, μ (x, x, x) ≠ 0) →
        AtomsAtLeast μ s → ¬ DistHasEmbedding ℤ μ →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ A : Finset (Fin n → Sig),
          α ≤ ∑ x ∈ A, tensorPow ν n x → β ≤ tripleProb μ n A := by sorry

end RestrictedAP.Counting
