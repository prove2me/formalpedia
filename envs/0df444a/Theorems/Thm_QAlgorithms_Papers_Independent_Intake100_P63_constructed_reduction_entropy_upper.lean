-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_constructed_reduction_entropy_upper
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.constructed_reduction_entropy_upper
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:24:37.896683+00:00
-- url     : https://prove2.me/theorems/8c93df17-56f2-4e54-b814-2496883eea27
-- title:
--   Lemma III.10: entropy upper bound for the constructed reductions
-- statement:
--   Let $\theta\in H\otimes H_E$ be a unit vector, with $H_E$ a copy of the nonzero finite-dimensional space $H$, and put $\rho=\operatorname{Tr}_E|\theta\rangle\langle\theta|$, assuming $\lambda_{\max}(\rho)<1$. For $N=n-m$, use the normalized symmetric expansion
--   $$
--   \Psi_{n,m,r}=\sum_{k=0}^{r}\beta_k\operatorname{Sym}(\eta_k\otimes\theta^{\otimes(N-k)}),\qquad \sum_k|\beta_k|^2=1,
--   $$
--   where every active $\eta_k$ is normalized, symmetric, and lies in $(\theta^\perp)^{\otimes k}$, and $\operatorname{Sym}$ denotes normalized symmetrization. Define the unnormalized vector $\Phi_{n,m,r}$ by retaining exactly the terms with $|\beta_k|\ge1/n$. Whenever this vector is nonzero, set $\pi_n=\operatorname{Tr}_{1,\ldots,r}\operatorname{Tr}_E|\Phi_{n,m,r}\rangle\langle\Phi_{n,m,r}|/\|\Phi_{n,m,r}\|^2$.
--
--   Take integer sequences $m=m(n)$ and $r=r(n)$ with $m+r\le n$ for positive $n$, $m,r=o(n)$, and the corresponding normalized original expansions. The cutoff reduction is normalized for sufficiently large $n$. With $S_2$ the von Neumann entropy in bits,
--   $$
--   S_2(\pi_n)\le nS_2(\rho)+o(n).
--   $$
--   Precisely, for every $\epsilon>0$, the inequality $S_2(\pi_n)\le nS_2(\rho)+\epsilon n$ holds for all sufficiently large $n$.
--
--   The printed k,r=o(n) is read as m,r=o(n), because k is the expansion index. The asymptotic entropy upper bound is never a field of the expansion data.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 25, Lemma III.10: entropy upper bound for the constructed reductions

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

/-- PDF p.25 Lemma III.10 Eq.(156), Eq.(115) on p.20. SOURCE INDEX CORRECTION:
printed k,r=o(n) is m,r=o(n); k is the summation index, not a sequence parameter.
The upper o(n) statement is expressed by every positive linear slack eventually. -/
theorem constructed_reduction_entropy_upper {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (theta : Vec (I × I)) (htheta : IsState theta) (hmixed : MixedMarginal theta)
    (m r : ℕ → ℕ) (hm : Sublinear m) (hr : Sublinear r)
    (hrange : ∀ n, 0 < n → m n + r n ≤ n)
    (D : (n : ℕ) → Expansion theta (n - m n) (r n)) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop,
      vnEntropy (cutoffReduction (D n) n) ≤
        (n : ℝ) * vnEntropy (traceRight (pureDensity theta)) + eps * n := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
