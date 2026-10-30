-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_keylPrefixAlignment
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.keylPrefixAlignment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:59:29.55169+00:00
-- url     : https://prove2.me/theorems/4a41a6bc-c68d-40f8-b5c3-a68bd736aad3
-- title:
--   Corollary 5.2: Keyl prefix alignment deficit
-- statement:
--   Let $d\ge1$ and let $\rho\in\mathbb C^{d\times d}$ be positive semidefinite of trace one, with nonincreasing spectrum $\alpha$. On $n\ge1$ copies the concrete Keyl experiment draws a weak-Schur shape $\lambda$ and then $V\sim K_\lambda(\rho)$. Its rank-$k$ report is $\widehat\rho_k=V\operatorname{diag}(\lambda_1/n,\ldots,\lambda_k/n,0,\ldots,0)V^\dagger$, with no renormalization, for $1\le k\le d$. Write $R_k=\mathbb E D_{H^2}(\widehat\rho_k,\rho)$, where $D_{H^2}(A,B)=\operatorname{Tr}((\sqrt A-\sqrt B)^2)$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. The full report has $k=d$. Work in the Section 5.1 eigenbasis $\rho=\operatorname{diag}(\alpha)$ and put $R=V^\dagger\rho V$. Conditional on $V$, choose any measurable permutation mixture satisfying $\Pr\{\pi(i)=a\mid V\}=|V_{a i}|^2$. The prefix parameter is $1\le j\le d$.
--
--   $$
--   \mathbb E\sum_{i=1}^j(\alpha_i-R_{ii})=\mathbb E\sum_{i=1}^j(\alpha_i-\alpha_{\pi(i)})\le\mathbb E[\bar\lambda_{\le j}-\alpha_{\le j}]+\frac{jd}{n}.
--   $$
--
--   This is a sample-complexity or risk guarantee for the concrete collective measurement and public decoder; it asserts no gate bound.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 23, Corollary 5.2

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

/-- Corollary 5.2, PDF p.23: equality with the induced-permutation deficit
AND the upper bound. rho is diagonal in the Section 5.1 basis; the kernel
has actual |V_(a,i)|^2 marginals, not an assumed alignment bound. -/
theorem keylPrefixAlignment {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (alpha : Fin d → ℝ) (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hRho : IsDensityMatrix rho)
    (hDiagonal : rho = Matrix.diagonal (fun i => (alpha i : ℂ))) (P : InducedPermutation d)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d) :
    keylMean hd hn rho hRho (fun V => ∑ i : Fin d, if i.val < j then
      alpha i - ((star (V : Matrix (Fin d) (Fin d) ℂ) * rho *
        (V : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i i).re else 0) =
      permutationMean hd hn rho hRho 1 P (fun pi => prefixMass alpha j - prefixMass (fun i => alpha (pi i)) j) ∧
    permutationMean hd hn rho hRho 1 P (fun pi => prefixMass alpha j - prefixMass (fun i => alpha (pi i)) j) ≤
      normalizedExcess alpha j n + (j : ℝ) * d / n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
