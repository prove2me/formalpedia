-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_cutoff_operator_domination
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.cutoff_operator_domination
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:23:25.086427+00:00
-- url     : https://prove2.me/theorems/53d1e968-6c84-42b0-b6e8-306f99ab1844
-- title:
--   Lemma III.8: operator domination from a truncated expansion
-- statement:
--   Let $\theta\in H\otimes H_E$ be a unit vector, with $H_E$ a copy of the nonzero finite-dimensional space $H$, and put $\rho=\operatorname{Tr}_E|\theta\rangle\langle\theta|$, assuming $\lambda_{\max}(\rho)<1$. For $N=n-m$, use the normalized symmetric expansion
--   $$
--   \Psi_{n,m,r}=\sum_{k=0}^{r}\beta_k\operatorname{Sym}(\eta_k\otimes\theta^{\otimes(N-k)}),\qquad \sum_k|\beta_k|^2=1,
--   $$
--   where every active $\eta_k$ is normalized, symmetric, and lies in $(\theta^\perp)^{\otimes k}$, and $\operatorname{Sym}$ denotes normalized symmetrization. Define the unnormalized vector $\Phi_{n,m,r}$ by retaining exactly the terms with $|\beta_k|\ge1/n$. Whenever this vector is nonzero, set $\pi_n=\operatorname{Tr}_{1,\ldots,r}\operatorname{Tr}_E|\Phi_{n,m,r}\rangle\langle\Phi_{n,m,r}|/\|\Phi_{n,m,r}\|^2$.
--
--   Assume $n>m\ge0$, $r\le n-m$, and that the retained index set is nonempty. Let $k_{\max}$ be its maximum and assume $2k_{\max}\le n-m$. Writing $h_2$ for binary entropy in bits, one has
--   $$
--   (|\theta\rangle\langle\theta|)^{\otimes(n-m-r)}
--   \le2^{n h_2(r/(n-m))}n^2\operatorname{Tr}_{1,\ldots,r}|\Phi_{n,m,r}\rangle\langle\Phi_{n,m,r}|.
--   $$
--
--   Phi remains unnormalized. The source restricts k_max, and its full range of r is retained; the entropy-monotonicity step in the printed proof needs separate independent scrutiny.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 20, Lemma III.8: operator domination from a truncated expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.20 Lemma III.8 Eq.(116): UNNORMALIZED cutoff Phi and the full
source range r≤n-m. Only k_max, not r, is assumed at most (n-m)/2. -/
theorem cutoff_operator_domination {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (theta : Vec (I × I)) (htheta : IsState theta) (hmixed : MixedMarginal theta)
    (n m r : ℕ) (hn : 0 < n) (hm : m < n)
    (D : Expansion theta (n - m) r)
    (hretained : (retainedCoefficientIndices D n).Nonempty)
    (hmax : 2 * (retainedCoefficientIndices D n).sup Fin.val ≤ n - m) :
    ((((2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((r : ℝ) / (n - m : ℕ))) * n ^ 2 : ℝ) : ℂ) •
      discardPrefix r D.range (pureDensity (cutoffVector D n)) -
        pureDensity (tensorPow (n - m - r) theta)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
