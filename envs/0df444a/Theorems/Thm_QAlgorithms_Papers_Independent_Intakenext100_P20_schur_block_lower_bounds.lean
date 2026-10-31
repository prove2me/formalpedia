-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P20_schur_block_lower_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P20.schur_block_lower_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:41:31.602099+00:00
-- url     : https://prove2.me/theorems/012e8153-b187-4846-a62c-5d31316a1ae0
-- title:
--   Lemma 11 lower bounds (B6), (B8)
-- statement:
--   Let $d,n\ge1$ and let $\rho$ be a normalized density matrix with decreasing spectrum $a=(a_1,\ldots,a_d)$, allowing zeros. For a Young index $\lambda\in Y_n$, let $P_\lambda$ be the orthogonal projector onto its full Schur-Weyl isotypic block and let $b_\lambda=\lambda/n$. Write $D$ for extended classical relative entropy, and put $c_{d,n}=(n+d)^{-d(d+1)/2}$. For every $\lambda$,
--
--   $$c_{d,n}\exp[-nD(b_\lambda\Vert a)]\le\operatorname{Tr}(P_\lambda\rho^{\otimes n}).$$
--
--   For any subset $A$ of the probability simplex, let $T_A=\{\lambda\in Y_n:b_\lambda\in A\}$ and $D_A=\inf_{\lambda\in T_A}D(b_\lambda\Vert a)$. Then
--
--   $$c_{d,n}\exp(-nD_A)\le\sum_{\lambda\in T_A}\operatorname{Tr}(P_\lambda\rho^{\otimes n}).$$
--
--   If $T_A$ is nonempty, the finite minimum $D_A$ is attained, including when every value is infinite. If $T_A$ is empty, $D_A=+\infty$ and the left side is zero. Positive empirical mass outside the spectral support also gives a zero exponential. These are precisely the lower clauses (B6), (B8), without the defective upper-bound constants.
-- source:
--   Exponents of quantum fixed-length pure state source coding, arXiv:quant-ph/0202002v6, PDF p. 10, Lemma 11 lower bounds (B6), (B8)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P20

noncomputable section

open scoped Matrix ENNReal ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P20

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P47 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P53 (SpectralData)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Dependency50.P28 (classicalD)

attribute [local instance] Classical.propDecidable

/-- Lemma 11, PDF p.10: lower bounds (B6), (B8), including attainment of
the finite type minimum when nonempty and zero contribution for an empty event. -/
theorem schur_block_lower_bounds {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (rho : {M : Matrix (Fin d) (Fin d) ℂ // IsDensityMatrix M})
    (spectral : SpectralData rho.val) (A : Set (Fin d → ℝ))
    (hA : ∀ b ∈ A, IsProbability b) :
    (∀ shape : Schur.Partition d n,
      lowerPrefactor d n * expNegD n
        ((classicalD (.finite 1 (by norm_num)) (Schur.normalizedRows hd hn shape) spectral.value).toENNReal) ≤ blockMass rho.val shape) ∧
    lowerPrefactor d n * expNegD n (eventD hd hn spectral.value A) ≤
      ∑ shape ∈ eventTypes hd hn A, blockMass rho.val shape ∧
    ((eventTypes hd hn A).Nonempty →
      ∃ shape ∈ eventTypes hd hn A,
        (classicalD (.finite 1 (by norm_num)) (Schur.normalizedRows hd hn shape) spectral.value).toENNReal =
          eventD hd hn spectral.value A) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P20

end
