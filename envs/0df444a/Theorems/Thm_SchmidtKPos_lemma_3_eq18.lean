-- Prove2me | Theorems.Thm_SchmidtKPos_lemma_3_eq18
-- name    : SchmidtKPos.lemma_3_eq18
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:52:09.842104+00:00
-- url     : https://prove2.me/theorems/580e99a0-35d1-470c-b3d5-9e10de7fc270
-- title:
--   Lemma 3, Eq. (18), p.4 — $k$-positivity is tested on maximally entangled vectors (corrected: $k\le n$)
-- statement:
--   Let $k\le n$ and let $\Lambda:\mathcal M_n(\mathbb C)\to\mathcal M_m(\mathbb C)$ be linear and Hermiticity preserving. Then $\Lambda$ is $k$-positive if and only if
--
--   $$
--   (\mathbf 1\otimes\Lambda)(|\Psi_k\rangle\langle\Psi_k|)\ge 0
--   $$
--
--   for all $|\Psi_k\rangle\in\mathcal H_n\otimes\mathcal H_n$ which are maximally entangled Schmidt rank $k$ vectors.
--
--   This reduces $k$-positivity to a test on a smaller family of pure states, and it underlies Eq. (19).
--
--   Differences from the source:
--   - correction: Eq. (18) for every k → adds the hypothesis k ≤ n; reason: for k > n the right side is vacuous, and n = m = 1, k = 2, Λ = −id is Hermiticity preserving and not 2-positive (machine-checked in Solutions/verification/SchmidtKPos_sanity.lean)
--   - generalization: Λ with output dimension not named in Lemma 3 → any linear Λ : M_n → M_m; reason: the argument does not use m = n; m = n gives the source statement
--   - reading: maximally entangled Schmidt rank k vectors → k^{-1/2} Σ_{i<k} γ_i ⊗ a_i with orthonormal families γ, a; reason: Eq. (1) with all λ_i = 1/k, the form used in Eqs. (10) and (20)
--   - reading: 1 ⊗ Λ of Definition 2, the dimension of 1 unnamed → the identity acts on H_n, the input dimension of Λ (S_k lives on H_n ⊗ H_n); reason: Definition 2 quantifies over S_k, which p.1 defines on H_n ⊗ H_n
--   - encoding: any decomposition {p_i ≥ 0, |ψ_i⟩} of ρ (Definition 1) → finite families indexed by Fin r, with unit vectors ψ_i and zero weights allowed; reason: in finite dimension a countable decomposition reduces to a finite one (Carathéodory) and a non-unit vector is absorbed into its weight; the same states result
--   - reading: the range of k (and of n in H_n) is left unstated → every natural number k and n, including 0; reason: never the weaker reading; at k = 0 the set S_0 is empty and at n = 0 there are no density matrices, so nothing is lost for k, n ≥ 1
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, Lemma 3, Eq. (18), p. 4

import Mathlib
import Definitions.Def_SchmidtKPos_IsKPositive
import Definitions.Def_SchmidtKPos_IsMaxEntangledRank
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

open QAlgorithms.Papers.Independent.Dependency50.P50 (PreservesHermiticity)

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, Lemma 3, Eq. (18), p.4: a linear Hermiticity-preserving `Λ` is
`k`-positive iff `(1 ⊗ Λ)(|Ψ_k⟩⟨Ψ_k|) ≥ 0` for all maximally entangled Schmidt rank `k` vectors.

**Formalization Note.** Corrected: the hypothesis `k ≤ n` is added. For `k > n` there are no
maximally entangled rank-`k` vectors in `H_n ⊗ H_n`, so the right side is vacuous, while
`n = m = 1`, `k = 2`, `Λ = −id` is not `2`-positive. The output dimension `m` is arbitrary. -/
theorem lemma_3_eq18 {n m k : ℕ} (hkn : k ≤ n)
    (Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (hΛ : PreservesHermiticity Λ) :
    IsKPositive k Λ ↔
      ∀ v : EuclideanSpace ℂ (Fin n × Fin n), IsMaxEntangledRank k v →
        (QAlgorithms.idTensorSuperop (R := Fin n) (⇑Λ)
          (QAlgorithms.pureDensity v)).PosSemidef := by sorry

end SchmidtKPos
