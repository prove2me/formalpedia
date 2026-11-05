-- Prove2me | Theorems.Thm_SchmidtKPos_lemma_3_eq19
-- name    : SchmidtKPos.lemma_3_eq19
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:51:54.359595+00:00
-- url     : https://prove2.me/theorems/580ad757-3d8f-4c19-b493-cc33ae469a70
-- title:
--   Lemma 3, Eq. (19), p.4 — coefficient criterion for $k$-positivity (corrected: $k\le n$, $k\le m$)
-- statement:
--   Let $k\le n$, $k\le m$, and let $\Lambda:\mathcal M_n(\mathbb C)\to\mathcal M_m(\mathbb C)$ be linear and Hermiticity preserving. Then $\Lambda$ is $k$-positive if and only if
--
--   $$
--   \sum_{i,j=1}^k\sqrt{\mu_i\mu_j}\,\langle b_i|\,\Lambda(|a_i\rangle\langle a_j|)\,|b_j\rangle\ge 0
--   $$
--
--   for all orthonormal families $\{|a_i\rangle\}_{i=1}^k\subset\mathbb C^n$ and $\{|b_i\rangle\}_{i=1}^k\subset\mathbb C^m$, and all Schmidt coefficients $\mu_i\ge 0$ with $\sum_{i=1}^k\mu_i=1$.
--
--   This is the form of $k$-positivity to which the proof of Theorem 1 compares Eq. (26).
--
--   Differences from the source:
--   - correction: Eq. (19) for every k → adds the hypotheses k ≤ n and k ≤ m; reason: otherwise no such orthogonal families exist and the right side is vacuous, and n = m = 1, k = 2, Λ = −id is Hermiticity preserving and not 2-positive (machine-checked in Solutions/verification/SchmidtKPos_sanity.lean)
--   - generalization: Λ with output dimension not named in Lemma 3 → any linear Λ : M_n → M_m; reason: the argument does not use m = n; m = n gives the source statement
--   - reading: orthogonal sets of vectors and Schmidt coefficients {μ_n}, Σ μ_n = 1 → orthonormal families a, b and real μ_i ≥ 0 with Σ μ_i = 1; reason: the Schmidt convention of Eq. (1), with unit vectors and nonnegative coefficients
--   - encoding: ≥ 0 and < 0 for a real quantity → the ComplexOrder relations on ℂ, which also assert that the value is real; reason: the quantity is real in every instance the source considers, so the condition is the same
--   - reading: 1 ⊗ Λ of Definition 2, the dimension of 1 unnamed → the identity acts on H_n, the input dimension of Λ (S_k lives on H_n ⊗ H_n); reason: Definition 2 quantifies over S_k, which p.1 defines on H_n ⊗ H_n
--   - encoding: any decomposition {p_i ≥ 0, |ψ_i⟩} of ρ (Definition 1) → finite families indexed by Fin r, with unit vectors ψ_i and zero weights allowed; reason: in finite dimension a countable decomposition reduces to a finite one (Carathéodory) and a non-unit vector is absorbed into its weight; the same states result
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, Lemma 3, Eq. (19), p. 4

import Mathlib
import Definitions.Def_SchmidtKPos_IsKPositive
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

open QAlgorithms.Papers.Independent.Dependency50.P50 (PreservesHermiticity)

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, Lemma 3, Eq. (19), p.4: a linear Hermiticity-preserving `Λ` is
`k`-positive iff `Σ_{n,m=1}^k √(μ_n μ_m) ⟨b_n| Λ(|a_n⟩⟨a_m|) |b_m⟩ ≥ 0` for all orthogonal sets
`{|a_n⟩}`, `{|b_n⟩}` and Schmidt coefficients `{μ_n}`, `Σ_n μ_n = 1`.

**Formalization Note.** Corrected: the hypotheses `k ≤ n` and `k ≤ m` are added. The `a`s live in
the input space and the `b`s in the output space; otherwise no such families exist, the right
side is vacuous, and `n = m = 1`, `k = 2`, `Λ = −id` is a counterexample. "Orthogonal sets" are
orthonormal families, and `μ_i ≥ 0` is the convention of Eq. (1). `vecMulVec a (star a')` is
`|a⟩⟨a'|` and `star b ⬝ᵥ (M *ᵥ b')` is `⟨b|M|b'⟩`. `0 ≤` on `ℂ` includes reality. -/
theorem lemma_3_eq19 {n m k : ℕ} (hkn : k ≤ n) (hkm : k ≤ m)
    (Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (hΛ : PreservesHermiticity Λ) :
    IsKPositive k Λ ↔
      ∀ (a : Fin k → EuclideanSpace ℂ (Fin n)) (b : Fin k → EuclideanSpace ℂ (Fin m)),
        Orthonormal ℂ a → Orthonormal ℂ b →
        ∀ μ : Fin k → ℝ, (∀ i, 0 ≤ μ i) → ∑ i, μ i = 1 →
          0 ≤ ∑ i, ∑ j, (Real.sqrt (μ i * μ j) : ℂ) *
            (star (WithLp.ofLp (b i)) ⬝ᵥ
              (Λ (Matrix.vecMulVec (WithLp.ofLp (a i)) (star (WithLp.ofLp (a j)))) *ᵥ
                WithLp.ofLp (b j))) := by sorry

end SchmidtKPos
