-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_truncatedKeylErrorReduction
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.truncatedKeylErrorReduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:02:34.193155+00:00
-- url     : https://prove2.me/theorems/101fe310-5c73-450f-acd9-7d4ac83fdae4
-- title:
--   Theorem 5.6: Truncated Keyl Hellinger error reduction
-- statement:
--   Let $d\ge1$ and let $\rho\in\mathbb C^{d\times d}$ be positive semidefinite of trace one, with nonincreasing spectrum $\alpha$. On $n\ge1$ copies the concrete Keyl experiment draws a weak-Schur shape $\lambda$ and then $V\sim K_\lambda(\rho)$. Its rank-$k$ report is $\widehat\rho_k=V\operatorname{diag}(\lambda_1/n,\ldots,\lambda_k/n,0,\ldots,0)V^\dagger$, with no renormalization, for $1\le k\le d$. Write $R_k=\mathbb E D_{H^2}(\widehat\rho_k,\rho)$, where $D_{H^2}(A,B)=\operatorname{Tr}((\sqrt A-\sqrt B)^2)$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. The full report has $k=d$. The constant $C>0$ is absolute and precedes all dimensions, sample counts, spectra and states. In any eigenbasis $B$, the conditional permutation mixture has marginals $\Pr\{\pi(i)=a\mid V\}=|(B^\dagger V)_{a i}|^2$. The bound holds for every measurable such mixture.
--
--   $$
--   R_k\le\alpha_{>k}+2\mathbb E\,d_{H^2}^{(k)}(\alpha\circ\pi,\alpha)+2\mathbb E[\bar\lambda_{\le k}-\alpha_{\le k}]+C\frac{kd}{n}.
--   $$
--
--   This is a sample-complexity or risk guarantee for the concrete collective measurement and public decoder; it asserts no gate bound.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 25, Theorem 5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P32

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Matrix ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Extend50.P32

open QAlgorithms.Papers.Independent.Support50.P38 (wordMass tv)

-- For the density matrices below, the characteristic-polynomial identity
-- preserves all eigenvalues with multiplicity and is equivalent to unitary
-- diagonalization with these real eigenvalues. No accuracy is assumed.

open QAlgorithms.Papers.Independent.Gap20.P17 (HasSpectrum)

/-- Theorem 5.6, PDF pp.25-26: permutation Hellinger term is truncated to k.
B is an actual eigenbasis; induced permutations use B dagger V. The rank-k
report is not renormalized, and the Keyl law is fixed concretely. -/
theorem truncatedKeylErrorReduction : ∃ C : ℝ, 0 < C ∧
    ∀ (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (alpha : Fin d → ℝ),
      Learning.IsDistribution alpha → Antitone alpha →
      ∀ (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho)
        (B : Matrix.unitaryGroup (Fin d) ℂ),
      rho = (B : Matrix _ _ ℂ) * Matrix.diagonal (fun i => (alpha i : ℂ)) * star (B : Matrix _ _ ℂ) →
      ∀ (P : InducedPermutation d) (k : ℕ), 1 ≤ k → k ≤ d →
        keylRisk hd hn k rho hRho ≤ ENNReal.ofReal
          (tail alpha k + 2 * permutationMean hd hn rho hRho B P (fun pi => h2 k (fun i => alpha (pi i)) alpha) +
            2 * normalizedExcess alpha k n + C * k * d / n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
